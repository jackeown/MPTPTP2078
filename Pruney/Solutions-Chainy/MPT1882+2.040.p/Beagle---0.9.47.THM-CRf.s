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
% DateTime   : Thu Dec  3 10:30:18 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 5.04s
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

tff(f_133,negated_conjecture,(
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

tff(f_67,axiom,(
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

tff(f_113,axiom,(
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
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_80,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_61,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_63,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_52])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_334,plain,(
    ! [A_92,B_93] :
      ( '#skF_2'(A_92,B_93) != B_93
      | v3_tex_2(B_93,A_92)
      | ~ v2_tex_2(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_341,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_334])).

tff(c_345,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_341])).

tff(c_346,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_345])).

tff(c_347,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_558,plain,(
    ! [B_125,A_126] :
      ( v2_tex_2(B_125,A_126)
      | ~ v1_zfmisc_1(B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | v1_xboole_0(B_125)
      | ~ l1_pre_topc(A_126)
      | ~ v2_tdlat_3(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_565,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_558])).

tff(c_569,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_61,c_565])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_347,c_569])).

tff(c_572,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_573,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_740,plain,(
    ! [B_154,A_155] :
      ( r1_tarski(B_154,'#skF_2'(A_155,B_154))
      | v3_tex_2(B_154,A_155)
      | ~ v2_tex_2(B_154,A_155)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_155)))
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_745,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_740])).

tff(c_749,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_573,c_745])).

tff(c_750,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_749])).

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

tff(c_93,plain,(
    ! [C_44,B_45,A_46] :
      ( ~ v1_xboole_0(C_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [B_47,A_48,A_49] :
      ( ~ v1_xboole_0(B_47)
      | ~ r2_hidden(A_48,A_49)
      | ~ r1_tarski(A_49,B_47) ) ),
    inference(resolution,[status(thm)],[c_16,c_93])).

tff(c_105,plain,(
    ! [B_50,A_51,B_52] :
      ( ~ v1_xboole_0(B_50)
      | ~ r1_tarski(A_51,B_50)
      | r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_101])).

tff(c_112,plain,(
    ! [B_53,B_54] :
      ( ~ v1_xboole_0(B_53)
      | r1_tarski(B_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_12,c_105])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,(
    ! [B_54,B_53] :
      ( B_54 = B_53
      | ~ r1_tarski(B_54,B_53)
      | ~ v1_xboole_0(B_53) ) ),
    inference(resolution,[status(thm)],[c_112,c_8])).

tff(c_779,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_750,c_122])).

tff(c_794,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_572,c_779])).

tff(c_32,plain,(
    ! [B_25,A_23] :
      ( B_25 = A_23
      | ~ r1_tarski(A_23,B_25)
      | ~ v1_zfmisc_1(B_25)
      | v1_xboole_0(B_25)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_776,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_750,c_32])).

tff(c_791,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_572,c_776])).

tff(c_803,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_794,c_791])).

tff(c_615,plain,(
    ! [A_138,B_139] :
      ( v2_tex_2('#skF_2'(A_138,B_139),A_138)
      | v3_tex_2(B_139,A_138)
      | ~ v2_tex_2(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_620,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_615])).

tff(c_624,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_573,c_620])).

tff(c_625,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_624])).

tff(c_882,plain,(
    ! [A_162,B_163] :
      ( m1_subset_1('#skF_2'(A_162,B_163),k1_zfmisc_1(u1_struct_0(A_162)))
      | v3_tex_2(B_163,A_162)
      | ~ v2_tex_2(B_163,A_162)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [B_31,A_29] :
      ( v1_zfmisc_1(B_31)
      | ~ v2_tex_2(B_31,A_29)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_29)))
      | v1_xboole_0(B_31)
      | ~ l1_pre_topc(A_29)
      | ~ v2_tdlat_3(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1941,plain,(
    ! [A_249,B_250] :
      ( v1_zfmisc_1('#skF_2'(A_249,B_250))
      | ~ v2_tex_2('#skF_2'(A_249,B_250),A_249)
      | v1_xboole_0('#skF_2'(A_249,B_250))
      | ~ v2_tdlat_3(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249)
      | v3_tex_2(B_250,A_249)
      | ~ v2_tex_2(B_250,A_249)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249) ) ),
    inference(resolution,[status(thm)],[c_882,c_38])).

tff(c_1950,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_625,c_1941])).

tff(c_1965,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_573,c_48,c_46,c_1950])).

tff(c_1967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_50,c_794,c_803,c_1965])).

tff(c_1969,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1968,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2089,plain,(
    ! [B_288,A_289] :
      ( v2_tex_2(B_288,A_289)
      | ~ v3_tex_2(B_288,A_289)
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0(A_289)))
      | ~ l1_pre_topc(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2096,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_2089])).

tff(c_2100,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1968,c_2096])).

tff(c_2743,plain,(
    ! [B_369,A_370] :
      ( v1_zfmisc_1(B_369)
      | ~ v2_tex_2(B_369,A_370)
      | ~ m1_subset_1(B_369,k1_zfmisc_1(u1_struct_0(A_370)))
      | v1_xboole_0(B_369)
      | ~ l1_pre_topc(A_370)
      | ~ v2_tdlat_3(A_370)
      | ~ v2_pre_topc(A_370)
      | v2_struct_0(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2753,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_2743])).

tff(c_2758,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_2100,c_2753])).

tff(c_2760,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_42,c_1969,c_2758])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:30:31 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.96  
% 4.79/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.96  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.79/1.96  
% 4.79/1.96  %Foreground sorts:
% 4.79/1.96  
% 4.79/1.96  
% 4.79/1.96  %Background operators:
% 4.79/1.96  
% 4.79/1.96  
% 4.79/1.96  %Foreground operators:
% 4.79/1.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.79/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.79/1.96  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.79/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.79/1.96  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.79/1.96  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.79/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.79/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.79/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.96  tff('#skF_4', type, '#skF_4': $i).
% 4.79/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.79/1.96  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.79/1.96  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.79/1.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.79/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.79/1.96  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.79/1.96  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.79/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.79/1.96  
% 5.04/1.98  tff(f_133, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 5.04/1.98  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 5.04/1.98  tff(f_113, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 5.04/1.98  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.04/1.98  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.04/1.98  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.04/1.98  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.04/1.98  tff(f_80, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.04/1.98  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.04/1.98  tff(c_42, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.04/1.98  tff(c_58, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.04/1.98  tff(c_61, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_58])).
% 5.04/1.98  tff(c_52, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.04/1.98  tff(c_63, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_52])).
% 5.04/1.98  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.04/1.98  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.04/1.98  tff(c_334, plain, (![A_92, B_93]: ('#skF_2'(A_92, B_93)!=B_93 | v3_tex_2(B_93, A_92) | ~v2_tex_2(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.04/1.98  tff(c_341, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_334])).
% 5.04/1.98  tff(c_345, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_341])).
% 5.04/1.98  tff(c_346, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_63, c_345])).
% 5.04/1.98  tff(c_347, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_346])).
% 5.04/1.98  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.04/1.98  tff(c_46, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.04/1.98  tff(c_558, plain, (![B_125, A_126]: (v2_tex_2(B_125, A_126) | ~v1_zfmisc_1(B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | v1_xboole_0(B_125) | ~l1_pre_topc(A_126) | ~v2_tdlat_3(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.04/1.98  tff(c_565, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_558])).
% 5.04/1.98  tff(c_569, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_61, c_565])).
% 5.04/1.98  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_347, c_569])).
% 5.04/1.98  tff(c_572, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_346])).
% 5.04/1.98  tff(c_573, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_346])).
% 5.04/1.98  tff(c_740, plain, (![B_154, A_155]: (r1_tarski(B_154, '#skF_2'(A_155, B_154)) | v3_tex_2(B_154, A_155) | ~v2_tex_2(B_154, A_155) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_155))) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.04/1.98  tff(c_745, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_740])).
% 5.04/1.98  tff(c_749, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_573, c_745])).
% 5.04/1.98  tff(c_750, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_63, c_749])).
% 5.04/1.98  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.04/1.98  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.04/1.98  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.04/1.98  tff(c_93, plain, (![C_44, B_45, A_46]: (~v1_xboole_0(C_44) | ~m1_subset_1(B_45, k1_zfmisc_1(C_44)) | ~r2_hidden(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.04/1.98  tff(c_101, plain, (![B_47, A_48, A_49]: (~v1_xboole_0(B_47) | ~r2_hidden(A_48, A_49) | ~r1_tarski(A_49, B_47))), inference(resolution, [status(thm)], [c_16, c_93])).
% 5.04/1.98  tff(c_105, plain, (![B_50, A_51, B_52]: (~v1_xboole_0(B_50) | ~r1_tarski(A_51, B_50) | r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_6, c_101])).
% 5.04/1.98  tff(c_112, plain, (![B_53, B_54]: (~v1_xboole_0(B_53) | r1_tarski(B_53, B_54))), inference(resolution, [status(thm)], [c_12, c_105])).
% 5.04/1.98  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.04/1.98  tff(c_122, plain, (![B_54, B_53]: (B_54=B_53 | ~r1_tarski(B_54, B_53) | ~v1_xboole_0(B_53))), inference(resolution, [status(thm)], [c_112, c_8])).
% 5.04/1.98  tff(c_779, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_750, c_122])).
% 5.04/1.98  tff(c_794, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_572, c_779])).
% 5.04/1.98  tff(c_32, plain, (![B_25, A_23]: (B_25=A_23 | ~r1_tarski(A_23, B_25) | ~v1_zfmisc_1(B_25) | v1_xboole_0(B_25) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.04/1.98  tff(c_776, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_750, c_32])).
% 5.04/1.98  tff(c_791, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_572, c_776])).
% 5.04/1.98  tff(c_803, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_794, c_791])).
% 5.04/1.98  tff(c_615, plain, (![A_138, B_139]: (v2_tex_2('#skF_2'(A_138, B_139), A_138) | v3_tex_2(B_139, A_138) | ~v2_tex_2(B_139, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.04/1.98  tff(c_620, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_615])).
% 5.04/1.98  tff(c_624, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_573, c_620])).
% 5.04/1.98  tff(c_625, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_63, c_624])).
% 5.04/1.98  tff(c_882, plain, (![A_162, B_163]: (m1_subset_1('#skF_2'(A_162, B_163), k1_zfmisc_1(u1_struct_0(A_162))) | v3_tex_2(B_163, A_162) | ~v2_tex_2(B_163, A_162) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.04/1.98  tff(c_38, plain, (![B_31, A_29]: (v1_zfmisc_1(B_31) | ~v2_tex_2(B_31, A_29) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_29))) | v1_xboole_0(B_31) | ~l1_pre_topc(A_29) | ~v2_tdlat_3(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.04/1.98  tff(c_1941, plain, (![A_249, B_250]: (v1_zfmisc_1('#skF_2'(A_249, B_250)) | ~v2_tex_2('#skF_2'(A_249, B_250), A_249) | v1_xboole_0('#skF_2'(A_249, B_250)) | ~v2_tdlat_3(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249) | v3_tex_2(B_250, A_249) | ~v2_tex_2(B_250, A_249) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249))), inference(resolution, [status(thm)], [c_882, c_38])).
% 5.04/1.98  tff(c_1950, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_625, c_1941])).
% 5.04/1.98  tff(c_1965, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_573, c_48, c_46, c_1950])).
% 5.04/1.98  tff(c_1967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_50, c_794, c_803, c_1965])).
% 5.04/1.98  tff(c_1969, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 5.04/1.98  tff(c_1968, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_58])).
% 5.04/1.98  tff(c_2089, plain, (![B_288, A_289]: (v2_tex_2(B_288, A_289) | ~v3_tex_2(B_288, A_289) | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0(A_289))) | ~l1_pre_topc(A_289))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.04/1.98  tff(c_2096, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_2089])).
% 5.04/1.98  tff(c_2100, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1968, c_2096])).
% 5.04/1.98  tff(c_2743, plain, (![B_369, A_370]: (v1_zfmisc_1(B_369) | ~v2_tex_2(B_369, A_370) | ~m1_subset_1(B_369, k1_zfmisc_1(u1_struct_0(A_370))) | v1_xboole_0(B_369) | ~l1_pre_topc(A_370) | ~v2_tdlat_3(A_370) | ~v2_pre_topc(A_370) | v2_struct_0(A_370))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.04/1.98  tff(c_2753, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_2743])).
% 5.04/1.98  tff(c_2758, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_2100, c_2753])).
% 5.04/1.98  tff(c_2760, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_42, c_1969, c_2758])).
% 5.04/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.04/1.98  
% 5.04/1.98  Inference rules
% 5.04/1.98  ----------------------
% 5.04/1.98  #Ref     : 0
% 5.04/1.98  #Sup     : 563
% 5.04/1.98  #Fact    : 0
% 5.04/1.98  #Define  : 0
% 5.04/1.98  #Split   : 19
% 5.04/1.98  #Chain   : 0
% 5.04/1.98  #Close   : 0
% 5.04/1.98  
% 5.04/1.98  Ordering : KBO
% 5.04/1.98  
% 5.04/1.98  Simplification rules
% 5.04/1.98  ----------------------
% 5.04/1.98  #Subsume      : 268
% 5.04/1.98  #Demod        : 252
% 5.04/1.98  #Tautology    : 57
% 5.04/1.98  #SimpNegUnit  : 69
% 5.04/1.98  #BackRed      : 0
% 5.04/1.98  
% 5.04/1.98  #Partial instantiations: 0
% 5.04/1.98  #Strategies tried      : 1
% 5.04/1.98  
% 5.04/1.98  Timing (in seconds)
% 5.04/1.98  ----------------------
% 5.04/1.98  Preprocessing        : 0.31
% 5.04/1.98  Parsing              : 0.17
% 5.04/1.98  CNF conversion       : 0.02
% 5.04/1.98  Main loop            : 0.82
% 5.04/1.98  Inferencing          : 0.27
% 5.04/1.98  Reduction            : 0.20
% 5.04/1.98  Demodulation         : 0.13
% 5.04/1.98  BG Simplification    : 0.03
% 5.04/1.98  Subsumption          : 0.27
% 5.04/1.98  Abstraction          : 0.03
% 5.04/1.98  MUC search           : 0.00
% 5.04/1.98  Cooper               : 0.00
% 5.04/1.98  Total                : 1.17
% 5.04/1.98  Index Insertion      : 0.00
% 5.04/1.98  Index Deletion       : 0.00
% 5.04/1.98  Index Matching       : 0.00
% 5.04/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
