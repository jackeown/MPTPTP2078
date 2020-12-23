%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:17 EST 2020

% Result     : Theorem 5.41s
% Output     : CNFRefutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 337 expanded)
%              Number of leaves         :   28 ( 127 expanded)
%              Depth                    :   12
%              Number of atoms          :  230 (1228 expanded)
%              Number of equality atoms :   14 (  57 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_117,negated_conjecture,(
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

tff(f_65,axiom,(
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

tff(f_97,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_54,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_60,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_48])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_277,plain,(
    ! [A_59,B_60] :
      ( '#skF_2'(A_59,B_60) != B_60
      | v3_tex_2(B_60,A_59)
      | ~ v2_tex_2(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_280,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_277])).

tff(c_283,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_280])).

tff(c_284,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_283])).

tff(c_285,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1043,plain,(
    ! [B_82,A_83] :
      ( v2_tex_2(B_82,A_83)
      | ~ v1_zfmisc_1(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | v1_xboole_0(B_82)
      | ~ l1_pre_topc(A_83)
      | ~ v2_tdlat_3(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1046,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1043])).

tff(c_1049,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_58,c_1046])).

tff(c_1051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_285,c_1049])).

tff(c_1053,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_1178,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(B_87,'#skF_2'(A_88,B_87))
      | v3_tex_2(B_87,A_88)
      | ~ v2_tex_2(B_87,A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1180,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1178])).

tff(c_1183,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1053,c_1180])).

tff(c_1184,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1183])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(A_34,B_35)
      | ~ r1_tarski(k1_tarski(A_34),B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_94,plain,(
    ! [A_38] : r2_hidden(A_38,k1_tarski(A_38)) ),
    inference(resolution,[status(thm)],[c_10,c_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_38] : ~ v1_xboole_0(k1_tarski(A_38)) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k1_tarski(A_7),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_114,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(A_43,B_42)
      | ~ v1_zfmisc_1(B_42)
      | v1_xboole_0(B_42)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_117,plain,(
    ! [A_7,B_8] :
      ( k1_tarski(A_7) = B_8
      | ~ v1_zfmisc_1(B_8)
      | v1_xboole_0(B_8)
      | v1_xboole_0(k1_tarski(A_7))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_14,c_114])).

tff(c_126,plain,(
    ! [A_44,B_45] :
      ( k1_tarski(A_44) = B_45
      | ~ v1_zfmisc_1(B_45)
      | v1_xboole_0(B_45)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_117])).

tff(c_138,plain,(
    ! [A_46] :
      ( k1_tarski('#skF_1'(A_46)) = A_46
      | ~ v1_zfmisc_1(A_46)
      | v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_4,c_126])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | ~ r1_tarski(k1_tarski(A_7),B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(A_47),B_48)
      | ~ r1_tarski(A_47,B_48)
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_12])).

tff(c_169,plain,(
    ! [B_48,A_47] :
      ( ~ v1_xboole_0(B_48)
      | ~ r1_tarski(A_47,B_48)
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_1187,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1184,c_169])).

tff(c_1195,plain,
    ( ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1187])).

tff(c_1196,plain,(
    ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1195])).

tff(c_1052,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_30,plain,(
    ! [B_22,A_20] :
      ( B_22 = A_20
      | ~ r1_tarski(A_20,B_22)
      | ~ v1_zfmisc_1(B_22)
      | v1_xboole_0(B_22)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1190,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1184,c_30])).

tff(c_1199,plain,
    ( ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1052,c_1190])).

tff(c_1203,plain,(
    ~ v1_zfmisc_1('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1196,c_1199])).

tff(c_1401,plain,(
    ! [A_96,B_97] :
      ( v2_tex_2('#skF_2'(A_96,B_97),A_96)
      | v3_tex_2(B_97,A_96)
      | ~ v2_tex_2(B_97,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1403,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1401])).

tff(c_1406,plain,
    ( v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1053,c_1403])).

tff(c_1407,plain,(
    v2_tex_2('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1406])).

tff(c_2370,plain,(
    ! [A_112,B_113] :
      ( m1_subset_1('#skF_2'(A_112,B_113),k1_zfmisc_1(u1_struct_0(A_112)))
      | v3_tex_2(B_113,A_112)
      | ~ v2_tex_2(B_113,A_112)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,(
    ! [B_25,A_23] :
      ( v1_zfmisc_1(B_25)
      | ~ v2_tex_2(B_25,A_23)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | v1_xboole_0(B_25)
      | ~ l1_pre_topc(A_23)
      | ~ v2_tdlat_3(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4617,plain,(
    ! [A_172,B_173] :
      ( v1_zfmisc_1('#skF_2'(A_172,B_173))
      | ~ v2_tex_2('#skF_2'(A_172,B_173),A_172)
      | v1_xboole_0('#skF_2'(A_172,B_173))
      | ~ v2_tdlat_3(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172)
      | v3_tex_2(B_173,A_172)
      | ~ v2_tex_2(B_173,A_172)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(resolution,[status(thm)],[c_2370,c_34])).

tff(c_4621,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1407,c_4617])).

tff(c_4625,plain,
    ( v1_zfmisc_1('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3')
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1053,c_44,c_42,c_4621])).

tff(c_4627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_46,c_1196,c_1203,c_4625])).

tff(c_4629,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4628,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_4697,plain,(
    ! [B_188,A_189] :
      ( v2_tex_2(B_188,A_189)
      | ~ v3_tex_2(B_188,A_189)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4700,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_4697])).

tff(c_4703,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4628,c_4700])).

tff(c_5556,plain,(
    ! [B_225,A_226] :
      ( v1_zfmisc_1(B_225)
      | ~ v2_tex_2(B_225,A_226)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_226)))
      | v1_xboole_0(B_225)
      | ~ l1_pre_topc(A_226)
      | ~ v2_tdlat_3(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5562,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_5556])).

tff(c_5566,plain,
    ( v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_4703,c_5562])).

tff(c_5568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_4629,c_5566])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:19:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.41/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.04  
% 5.41/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.04  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.41/2.04  
% 5.41/2.04  %Foreground sorts:
% 5.41/2.04  
% 5.41/2.04  
% 5.41/2.04  %Background operators:
% 5.41/2.04  
% 5.41/2.04  
% 5.41/2.04  %Foreground operators:
% 5.41/2.04  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.41/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.41/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.41/2.04  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.41/2.04  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.41/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.41/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.41/2.04  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.41/2.04  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.41/2.04  tff('#skF_3', type, '#skF_3': $i).
% 5.41/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.41/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.41/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.41/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.41/2.04  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.41/2.04  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.41/2.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.41/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.41/2.04  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.41/2.04  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 5.41/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.41/2.04  
% 5.41/2.06  tff(f_117, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 5.41/2.06  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 5.41/2.06  tff(f_97, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 5.41/2.06  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.41/2.06  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.41/2.06  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.41/2.06  tff(f_78, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.41/2.06  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.41/2.06  tff(c_38, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.41/2.06  tff(c_54, plain, (v3_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.41/2.06  tff(c_58, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 5.41/2.06  tff(c_48, plain, (~v1_zfmisc_1('#skF_4') | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.41/2.06  tff(c_60, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_48])).
% 5.41/2.06  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.41/2.06  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.41/2.06  tff(c_277, plain, (![A_59, B_60]: ('#skF_2'(A_59, B_60)!=B_60 | v3_tex_2(B_60, A_59) | ~v2_tex_2(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.41/2.06  tff(c_280, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_277])).
% 5.41/2.06  tff(c_283, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_280])).
% 5.41/2.06  tff(c_284, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_283])).
% 5.41/2.06  tff(c_285, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_284])).
% 5.41/2.06  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.41/2.06  tff(c_42, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.41/2.06  tff(c_1043, plain, (![B_82, A_83]: (v2_tex_2(B_82, A_83) | ~v1_zfmisc_1(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | v1_xboole_0(B_82) | ~l1_pre_topc(A_83) | ~v2_tdlat_3(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.41/2.06  tff(c_1046, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1043])).
% 5.41/2.06  tff(c_1049, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_58, c_1046])).
% 5.41/2.06  tff(c_1051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_285, c_1049])).
% 5.41/2.06  tff(c_1053, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_284])).
% 5.41/2.06  tff(c_1178, plain, (![B_87, A_88]: (r1_tarski(B_87, '#skF_2'(A_88, B_87)) | v3_tex_2(B_87, A_88) | ~v2_tex_2(B_87, A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.41/2.06  tff(c_1180, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1178])).
% 5.41/2.06  tff(c_1183, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1053, c_1180])).
% 5.41/2.06  tff(c_1184, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_1183])).
% 5.41/2.06  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.41/2.06  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.41/2.06  tff(c_74, plain, (![A_34, B_35]: (r2_hidden(A_34, B_35) | ~r1_tarski(k1_tarski(A_34), B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.41/2.06  tff(c_94, plain, (![A_38]: (r2_hidden(A_38, k1_tarski(A_38)))), inference(resolution, [status(thm)], [c_10, c_74])).
% 5.41/2.06  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.41/2.06  tff(c_98, plain, (![A_38]: (~v1_xboole_0(k1_tarski(A_38)))), inference(resolution, [status(thm)], [c_94, c_2])).
% 5.41/2.06  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.41/2.06  tff(c_114, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(A_43, B_42) | ~v1_zfmisc_1(B_42) | v1_xboole_0(B_42) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.41/2.06  tff(c_117, plain, (![A_7, B_8]: (k1_tarski(A_7)=B_8 | ~v1_zfmisc_1(B_8) | v1_xboole_0(B_8) | v1_xboole_0(k1_tarski(A_7)) | ~r2_hidden(A_7, B_8))), inference(resolution, [status(thm)], [c_14, c_114])).
% 5.41/2.06  tff(c_126, plain, (![A_44, B_45]: (k1_tarski(A_44)=B_45 | ~v1_zfmisc_1(B_45) | v1_xboole_0(B_45) | ~r2_hidden(A_44, B_45))), inference(negUnitSimplification, [status(thm)], [c_98, c_117])).
% 5.41/2.06  tff(c_138, plain, (![A_46]: (k1_tarski('#skF_1'(A_46))=A_46 | ~v1_zfmisc_1(A_46) | v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_4, c_126])).
% 5.41/2.06  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | ~r1_tarski(k1_tarski(A_7), B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.41/2.06  tff(c_161, plain, (![A_47, B_48]: (r2_hidden('#skF_1'(A_47), B_48) | ~r1_tarski(A_47, B_48) | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47))), inference(superposition, [status(thm), theory('equality')], [c_138, c_12])).
% 5.41/2.06  tff(c_169, plain, (![B_48, A_47]: (~v1_xboole_0(B_48) | ~r1_tarski(A_47, B_48) | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_161, c_2])).
% 5.41/2.06  tff(c_1187, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1184, c_169])).
% 5.41/2.06  tff(c_1195, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1187])).
% 5.41/2.06  tff(c_1196, plain, (~v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_1195])).
% 5.41/2.06  tff(c_1052, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(splitRight, [status(thm)], [c_284])).
% 5.41/2.06  tff(c_30, plain, (![B_22, A_20]: (B_22=A_20 | ~r1_tarski(A_20, B_22) | ~v1_zfmisc_1(B_22) | v1_xboole_0(B_22) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.41/2.06  tff(c_1190, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1184, c_30])).
% 5.41/2.06  tff(c_1199, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_1052, c_1190])).
% 5.41/2.06  tff(c_1203, plain, (~v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1196, c_1199])).
% 5.41/2.06  tff(c_1401, plain, (![A_96, B_97]: (v2_tex_2('#skF_2'(A_96, B_97), A_96) | v3_tex_2(B_97, A_96) | ~v2_tex_2(B_97, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.41/2.06  tff(c_1403, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1401])).
% 5.41/2.06  tff(c_1406, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1053, c_1403])).
% 5.41/2.06  tff(c_1407, plain, (v2_tex_2('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_1406])).
% 5.41/2.06  tff(c_2370, plain, (![A_112, B_113]: (m1_subset_1('#skF_2'(A_112, B_113), k1_zfmisc_1(u1_struct_0(A_112))) | v3_tex_2(B_113, A_112) | ~v2_tex_2(B_113, A_112) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.41/2.06  tff(c_34, plain, (![B_25, A_23]: (v1_zfmisc_1(B_25) | ~v2_tex_2(B_25, A_23) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | v1_xboole_0(B_25) | ~l1_pre_topc(A_23) | ~v2_tdlat_3(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.41/2.06  tff(c_4617, plain, (![A_172, B_173]: (v1_zfmisc_1('#skF_2'(A_172, B_173)) | ~v2_tex_2('#skF_2'(A_172, B_173), A_172) | v1_xboole_0('#skF_2'(A_172, B_173)) | ~v2_tdlat_3(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172) | v3_tex_2(B_173, A_172) | ~v2_tex_2(B_173, A_172) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(resolution, [status(thm)], [c_2370, c_34])).
% 5.41/2.06  tff(c_4621, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1407, c_4617])).
% 5.41/2.06  tff(c_4625, plain, (v1_zfmisc_1('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3') | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1053, c_44, c_42, c_4621])).
% 5.41/2.06  tff(c_4627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_46, c_1196, c_1203, c_4625])).
% 5.41/2.06  tff(c_4629, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 5.41/2.06  tff(c_4628, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 5.41/2.06  tff(c_4697, plain, (![B_188, A_189]: (v2_tex_2(B_188, A_189) | ~v3_tex_2(B_188, A_189) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.41/2.06  tff(c_4700, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_4697])).
% 5.41/2.06  tff(c_4703, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4628, c_4700])).
% 5.41/2.06  tff(c_5556, plain, (![B_225, A_226]: (v1_zfmisc_1(B_225) | ~v2_tex_2(B_225, A_226) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_226))) | v1_xboole_0(B_225) | ~l1_pre_topc(A_226) | ~v2_tdlat_3(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.41/2.06  tff(c_5562, plain, (v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_5556])).
% 5.41/2.06  tff(c_5566, plain, (v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_4703, c_5562])).
% 5.41/2.06  tff(c_5568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_4629, c_5566])).
% 5.41/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.06  
% 5.41/2.06  Inference rules
% 5.41/2.06  ----------------------
% 5.41/2.06  #Ref     : 0
% 5.41/2.06  #Sup     : 1315
% 5.41/2.06  #Fact    : 0
% 5.41/2.06  #Define  : 0
% 5.41/2.06  #Split   : 3
% 5.41/2.06  #Chain   : 0
% 5.41/2.06  #Close   : 0
% 5.41/2.06  
% 5.41/2.06  Ordering : KBO
% 5.41/2.06  
% 5.41/2.06  Simplification rules
% 5.41/2.06  ----------------------
% 5.41/2.06  #Subsume      : 477
% 5.41/2.06  #Demod        : 304
% 5.41/2.06  #Tautology    : 438
% 5.41/2.06  #SimpNegUnit  : 415
% 5.41/2.06  #BackRed      : 0
% 5.41/2.06  
% 5.41/2.06  #Partial instantiations: 0
% 5.41/2.06  #Strategies tried      : 1
% 5.41/2.06  
% 5.41/2.06  Timing (in seconds)
% 5.41/2.06  ----------------------
% 5.41/2.06  Preprocessing        : 0.30
% 5.41/2.06  Parsing              : 0.16
% 5.41/2.06  CNF conversion       : 0.02
% 5.41/2.06  Main loop            : 0.98
% 5.41/2.06  Inferencing          : 0.32
% 5.41/2.06  Reduction            : 0.30
% 5.41/2.06  Demodulation         : 0.19
% 5.41/2.06  BG Simplification    : 0.04
% 5.41/2.06  Subsumption          : 0.25
% 5.41/2.06  Abstraction          : 0.06
% 5.41/2.06  MUC search           : 0.00
% 5.41/2.06  Cooper               : 0.00
% 5.41/2.06  Total                : 1.32
% 5.41/2.06  Index Insertion      : 0.00
% 5.41/2.06  Index Deletion       : 0.00
% 5.41/2.06  Index Matching       : 0.00
% 5.41/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
