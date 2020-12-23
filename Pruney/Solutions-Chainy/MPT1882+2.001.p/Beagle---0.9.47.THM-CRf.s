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
% DateTime   : Thu Dec  3 10:30:12 EST 2020

% Result     : Theorem 4.24s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 301 expanded)
%              Number of leaves         :   26 ( 114 expanded)
%              Depth                    :   11
%              Number of atoms          :  217 (1136 expanded)
%              Number of equality atoms :   11 (  47 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_136,negated_conjecture,(
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

tff(f_83,axiom,(
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

tff(f_116,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_subset_1(B,A)
           => v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_54,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_58,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_936,plain,(
    ! [A_148,B_149] :
      ( '#skF_1'(A_148,B_149) != B_149
      | v3_tex_2(B_149,A_148)
      | ~ v2_tex_2(B_149,A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_943,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_936])).

tff(c_947,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_943])).

tff(c_948,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_947])).

tff(c_949,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_948])).

tff(c_44,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1047,plain,(
    ! [B_164,A_165] :
      ( v2_tex_2(B_164,A_165)
      | ~ v1_zfmisc_1(B_164)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | v1_xboole_0(B_164)
      | ~ l1_pre_topc(A_165)
      | ~ v2_tdlat_3(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1057,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_1047])).

tff(c_1062,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_56,c_1057])).

tff(c_1064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_949,c_1062])).

tff(c_1066,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_948])).

tff(c_1080,plain,(
    ! [B_168,A_169] :
      ( r1_tarski(B_168,'#skF_1'(A_169,B_168))
      | v3_tex_2(B_168,A_169)
      | ~ v2_tex_2(B_168,A_169)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1085,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_1080])).

tff(c_1089,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1066,c_1085])).

tff(c_1090,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1089])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_83,plain,(
    ! [B_38,A_39] :
      ( v1_xboole_0(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_90,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(A_5)
      | ~ v1_xboole_0(B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_83])).

tff(c_1096,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1090,c_90])).

tff(c_1102,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1096])).

tff(c_1065,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_948])).

tff(c_100,plain,(
    ! [B_42,A_43] :
      ( v1_subset_1(B_42,A_43)
      | B_42 = A_43
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_107,plain,(
    ! [A_5,B_6] :
      ( v1_subset_1(A_5,B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_100])).

tff(c_881,plain,(
    ! [B_138,A_139] :
      ( v1_xboole_0(B_138)
      | ~ v1_subset_1(B_138,A_139)
      | ~ m1_subset_1(B_138,k1_zfmisc_1(A_139))
      | ~ v1_zfmisc_1(A_139)
      | v1_xboole_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_910,plain,(
    ! [A_142,B_143] :
      ( v1_xboole_0(A_142)
      | ~ v1_subset_1(A_142,B_143)
      | ~ v1_zfmisc_1(B_143)
      | v1_xboole_0(B_143)
      | ~ r1_tarski(A_142,B_143) ) ),
    inference(resolution,[status(thm)],[c_8,c_881])).

tff(c_917,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(A_5)
      | ~ v1_zfmisc_1(B_6)
      | v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_107,c_910])).

tff(c_1093,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | '#skF_1'('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1090,c_917])).

tff(c_1099,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1065,c_38,c_1093])).

tff(c_1103,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1102,c_1099])).

tff(c_1067,plain,(
    ! [A_166,B_167] :
      ( v2_tex_2('#skF_1'(A_166,B_167),A_166)
      | v3_tex_2(B_167,A_166)
      | ~ v2_tex_2(B_167,A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1072,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_1067])).

tff(c_1076,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1072])).

tff(c_1077,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1076])).

tff(c_1079,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_1077])).

tff(c_24,plain,(
    ! [A_13,B_19] :
      ( m1_subset_1('#skF_1'(A_13,B_19),k1_zfmisc_1(u1_struct_0(A_13)))
      | v3_tex_2(B_19,A_13)
      | ~ v2_tex_2(B_19,A_13)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1183,plain,(
    ! [B_180,A_181] :
      ( v1_zfmisc_1(B_180)
      | ~ v2_tex_2(B_180,A_181)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_181)))
      | v1_xboole_0(B_180)
      | ~ l1_pre_topc(A_181)
      | ~ v2_tdlat_3(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1384,plain,(
    ! [A_215,B_216] :
      ( v1_zfmisc_1('#skF_1'(A_215,B_216))
      | ~ v2_tex_2('#skF_1'(A_215,B_216),A_215)
      | v1_xboole_0('#skF_1'(A_215,B_216))
      | ~ v2_tdlat_3(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215)
      | v3_tex_2(B_216,A_215)
      | ~ v2_tex_2(B_216,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(resolution,[status(thm)],[c_24,c_1183])).

tff(c_1390,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1079,c_1384])).

tff(c_1395,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_1066,c_44,c_42,c_1390])).

tff(c_1397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_46,c_1102,c_1103,c_1395])).

tff(c_1399,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1398,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1698,plain,(
    ! [B_269,A_270] :
      ( v2_tex_2(B_269,A_270)
      | ~ v3_tex_2(B_269,A_270)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0(A_270)))
      | ~ l1_pre_topc(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1705,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_1698])).

tff(c_1709,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1398,c_1705])).

tff(c_1825,plain,(
    ! [B_297,A_298] :
      ( v1_zfmisc_1(B_297)
      | ~ v2_tex_2(B_297,A_298)
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0(A_298)))
      | v1_xboole_0(B_297)
      | ~ l1_pre_topc(A_298)
      | ~ v2_tdlat_3(A_298)
      | ~ v2_pre_topc(A_298)
      | v2_struct_0(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1832,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_1825])).

tff(c_1836,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_1709,c_1832])).

tff(c_1838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_38,c_1399,c_1836])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:47:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.24/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.75  
% 4.24/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.75  %$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.24/1.75  
% 4.24/1.75  %Foreground sorts:
% 4.24/1.75  
% 4.24/1.75  
% 4.24/1.75  %Background operators:
% 4.24/1.75  
% 4.24/1.75  
% 4.24/1.75  %Foreground operators:
% 4.24/1.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.24/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.24/1.75  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.24/1.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.24/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.24/1.75  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 4.24/1.75  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.24/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.24/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.24/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.24/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.24/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.24/1.75  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.24/1.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.24/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.24/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.24/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.24/1.75  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 4.24/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.24/1.75  
% 4.24/1.77  tff(f_136, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 4.24/1.77  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 4.24/1.77  tff(f_116, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 4.24/1.77  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.24/1.77  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.24/1.77  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 4.24/1.77  tff(f_52, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) => v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tex_2)).
% 4.24/1.77  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.24/1.77  tff(c_38, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.24/1.77  tff(c_54, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.24/1.77  tff(c_56, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 4.24/1.77  tff(c_48, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.24/1.77  tff(c_58, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48])).
% 4.24/1.77  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.24/1.77  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.24/1.77  tff(c_936, plain, (![A_148, B_149]: ('#skF_1'(A_148, B_149)!=B_149 | v3_tex_2(B_149, A_148) | ~v2_tex_2(B_149, A_148) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.24/1.77  tff(c_943, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_936])).
% 4.24/1.77  tff(c_947, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_943])).
% 4.24/1.77  tff(c_948, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_947])).
% 4.24/1.77  tff(c_949, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_948])).
% 4.24/1.77  tff(c_44, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.24/1.77  tff(c_42, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.24/1.77  tff(c_1047, plain, (![B_164, A_165]: (v2_tex_2(B_164, A_165) | ~v1_zfmisc_1(B_164) | ~m1_subset_1(B_164, k1_zfmisc_1(u1_struct_0(A_165))) | v1_xboole_0(B_164) | ~l1_pre_topc(A_165) | ~v2_tdlat_3(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.24/1.77  tff(c_1057, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_1047])).
% 4.24/1.77  tff(c_1062, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_56, c_1057])).
% 4.24/1.77  tff(c_1064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_949, c_1062])).
% 4.24/1.77  tff(c_1066, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_948])).
% 4.24/1.77  tff(c_1080, plain, (![B_168, A_169]: (r1_tarski(B_168, '#skF_1'(A_169, B_168)) | v3_tex_2(B_168, A_169) | ~v2_tex_2(B_168, A_169) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.24/1.77  tff(c_1085, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_1080])).
% 4.24/1.77  tff(c_1089, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1066, c_1085])).
% 4.24/1.77  tff(c_1090, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_1089])).
% 4.24/1.77  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.24/1.77  tff(c_83, plain, (![B_38, A_39]: (v1_xboole_0(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.24/1.77  tff(c_90, plain, (![A_5, B_6]: (v1_xboole_0(A_5) | ~v1_xboole_0(B_6) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_8, c_83])).
% 4.24/1.77  tff(c_1096, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1090, c_90])).
% 4.24/1.77  tff(c_1102, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_1096])).
% 4.24/1.77  tff(c_1065, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_948])).
% 4.24/1.77  tff(c_100, plain, (![B_42, A_43]: (v1_subset_1(B_42, A_43) | B_42=A_43 | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.24/1.77  tff(c_107, plain, (![A_5, B_6]: (v1_subset_1(A_5, B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_8, c_100])).
% 4.24/1.77  tff(c_881, plain, (![B_138, A_139]: (v1_xboole_0(B_138) | ~v1_subset_1(B_138, A_139) | ~m1_subset_1(B_138, k1_zfmisc_1(A_139)) | ~v1_zfmisc_1(A_139) | v1_xboole_0(A_139))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.24/1.77  tff(c_910, plain, (![A_142, B_143]: (v1_xboole_0(A_142) | ~v1_subset_1(A_142, B_143) | ~v1_zfmisc_1(B_143) | v1_xboole_0(B_143) | ~r1_tarski(A_142, B_143))), inference(resolution, [status(thm)], [c_8, c_881])).
% 4.24/1.77  tff(c_917, plain, (![A_5, B_6]: (v1_xboole_0(A_5) | ~v1_zfmisc_1(B_6) | v1_xboole_0(B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_107, c_910])).
% 4.24/1.77  tff(c_1093, plain, (v1_xboole_0('#skF_3') | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | '#skF_1'('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1090, c_917])).
% 4.24/1.77  tff(c_1099, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1065, c_38, c_1093])).
% 4.24/1.77  tff(c_1103, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1102, c_1099])).
% 4.24/1.77  tff(c_1067, plain, (![A_166, B_167]: (v2_tex_2('#skF_1'(A_166, B_167), A_166) | v3_tex_2(B_167, A_166) | ~v2_tex_2(B_167, A_166) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.24/1.77  tff(c_1072, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_1067])).
% 4.24/1.77  tff(c_1076, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1072])).
% 4.24/1.77  tff(c_1077, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_1076])).
% 4.24/1.77  tff(c_1079, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_1077])).
% 4.24/1.77  tff(c_24, plain, (![A_13, B_19]: (m1_subset_1('#skF_1'(A_13, B_19), k1_zfmisc_1(u1_struct_0(A_13))) | v3_tex_2(B_19, A_13) | ~v2_tex_2(B_19, A_13) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.24/1.77  tff(c_1183, plain, (![B_180, A_181]: (v1_zfmisc_1(B_180) | ~v2_tex_2(B_180, A_181) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_181))) | v1_xboole_0(B_180) | ~l1_pre_topc(A_181) | ~v2_tdlat_3(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.24/1.77  tff(c_1384, plain, (![A_215, B_216]: (v1_zfmisc_1('#skF_1'(A_215, B_216)) | ~v2_tex_2('#skF_1'(A_215, B_216), A_215) | v1_xboole_0('#skF_1'(A_215, B_216)) | ~v2_tdlat_3(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215) | v3_tex_2(B_216, A_215) | ~v2_tex_2(B_216, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(resolution, [status(thm)], [c_24, c_1183])).
% 4.24/1.77  tff(c_1390, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1079, c_1384])).
% 4.24/1.77  tff(c_1395, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_1066, c_44, c_42, c_1390])).
% 4.24/1.77  tff(c_1397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_46, c_1102, c_1103, c_1395])).
% 4.24/1.77  tff(c_1399, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_54])).
% 4.24/1.77  tff(c_1398, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 4.24/1.77  tff(c_1698, plain, (![B_269, A_270]: (v2_tex_2(B_269, A_270) | ~v3_tex_2(B_269, A_270) | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0(A_270))) | ~l1_pre_topc(A_270))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.24/1.77  tff(c_1705, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_1698])).
% 4.24/1.77  tff(c_1709, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1398, c_1705])).
% 4.24/1.77  tff(c_1825, plain, (![B_297, A_298]: (v1_zfmisc_1(B_297) | ~v2_tex_2(B_297, A_298) | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0(A_298))) | v1_xboole_0(B_297) | ~l1_pre_topc(A_298) | ~v2_tdlat_3(A_298) | ~v2_pre_topc(A_298) | v2_struct_0(A_298))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.24/1.77  tff(c_1832, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_1825])).
% 4.24/1.77  tff(c_1836, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_1709, c_1832])).
% 4.24/1.77  tff(c_1838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_38, c_1399, c_1836])).
% 4.24/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.77  
% 4.24/1.77  Inference rules
% 4.24/1.77  ----------------------
% 4.24/1.77  #Ref     : 0
% 4.24/1.77  #Sup     : 332
% 4.24/1.77  #Fact    : 0
% 4.24/1.77  #Define  : 0
% 4.24/1.77  #Split   : 6
% 4.24/1.77  #Chain   : 0
% 4.24/1.77  #Close   : 0
% 4.24/1.77  
% 4.24/1.77  Ordering : KBO
% 4.24/1.77  
% 4.24/1.77  Simplification rules
% 4.24/1.77  ----------------------
% 4.24/1.77  #Subsume      : 97
% 4.24/1.77  #Demod        : 197
% 4.24/1.77  #Tautology    : 40
% 4.24/1.77  #SimpNegUnit  : 78
% 4.24/1.77  #BackRed      : 6
% 4.24/1.77  
% 4.24/1.77  #Partial instantiations: 0
% 4.24/1.77  #Strategies tried      : 1
% 4.24/1.77  
% 4.24/1.77  Timing (in seconds)
% 4.24/1.77  ----------------------
% 4.24/1.77  Preprocessing        : 0.32
% 4.24/1.77  Parsing              : 0.17
% 4.24/1.77  CNF conversion       : 0.02
% 4.24/1.77  Main loop            : 0.69
% 4.24/1.77  Inferencing          : 0.27
% 4.24/1.77  Reduction            : 0.18
% 4.24/1.77  Demodulation         : 0.11
% 4.24/1.77  BG Simplification    : 0.03
% 4.24/1.77  Subsumption          : 0.16
% 4.24/1.77  Abstraction          : 0.03
% 4.24/1.77  MUC search           : 0.00
% 4.24/1.77  Cooper               : 0.00
% 4.24/1.77  Total                : 1.04
% 4.24/1.77  Index Insertion      : 0.00
% 4.24/1.77  Index Deletion       : 0.00
% 4.24/1.77  Index Matching       : 0.00
% 4.24/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
