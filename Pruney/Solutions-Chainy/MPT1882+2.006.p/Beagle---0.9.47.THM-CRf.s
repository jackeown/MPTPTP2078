%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:13 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 340 expanded)
%              Number of leaves         :   26 ( 126 expanded)
%              Depth                    :   11
%              Number of atoms          :  217 (1273 expanded)
%              Number of equality atoms :   13 (  69 expanded)
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

tff(f_86,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_54,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_56,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46])).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_794,plain,(
    ! [A_135,B_136] :
      ( '#skF_1'(A_135,B_136) != B_136
      | v3_tex_2(B_136,A_135)
      | ~ v2_tex_2(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_801,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_794])).

tff(c_805,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_801])).

tff(c_806,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_805])).

tff(c_807,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_806])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_867,plain,(
    ! [B_151,A_152] :
      ( v2_tex_2(B_151,A_152)
      | ~ v1_zfmisc_1(B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | v1_xboole_0(B_151)
      | ~ l1_pre_topc(A_152)
      | ~ v2_tdlat_3(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_874,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_867])).

tff(c_878,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_54,c_874])).

tff(c_880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_807,c_878])).

tff(c_881,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_806])).

tff(c_882,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_806])).

tff(c_891,plain,(
    ! [B_155,A_156] :
      ( r1_tarski(B_155,'#skF_1'(A_156,B_155))
      | v3_tex_2(B_155,A_156)
      | ~ v2_tex_2(B_155,A_156)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_156)))
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_896,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_891])).

tff(c_900,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_882,c_896])).

tff(c_901,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_900])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [B_37,A_38] :
      ( v1_subset_1(B_37,A_38)
      | B_37 = A_38
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_98,plain,(
    ! [A_5,B_6] :
      ( v1_subset_1(A_5,B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_91])).

tff(c_81,plain,(
    ! [B_35,A_36] :
      ( ~ v1_subset_1(B_35,A_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_736,plain,(
    ! [A_123,B_124] :
      ( ~ v1_subset_1(A_123,B_124)
      | ~ v1_xboole_0(B_124)
      | ~ r1_tarski(A_123,B_124) ) ),
    inference(resolution,[status(thm)],[c_8,c_81])).

tff(c_743,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_98,c_736])).

tff(c_907,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | '#skF_1'('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_901,c_743])).

tff(c_913,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_881,c_907])).

tff(c_747,plain,(
    ! [B_125,A_126] :
      ( ~ v1_subset_1(B_125,A_126)
      | v1_xboole_0(B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_126))
      | ~ v1_zfmisc_1(A_126)
      | v1_xboole_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_769,plain,(
    ! [A_129,B_130] :
      ( ~ v1_subset_1(A_129,B_130)
      | v1_xboole_0(A_129)
      | ~ v1_zfmisc_1(B_130)
      | v1_xboole_0(B_130)
      | ~ r1_tarski(A_129,B_130) ) ),
    inference(resolution,[status(thm)],[c_8,c_747])).

tff(c_776,plain,(
    ! [A_5,B_6] :
      ( v1_xboole_0(A_5)
      | ~ v1_zfmisc_1(B_6)
      | v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_98,c_769])).

tff(c_904,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | '#skF_1'('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_901,c_776])).

tff(c_910,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_881,c_36,c_904])).

tff(c_914,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_913,c_910])).

tff(c_926,plain,(
    ! [A_159,B_160] :
      ( v2_tex_2('#skF_1'(A_159,B_160),A_159)
      | v3_tex_2(B_160,A_159)
      | ~ v2_tex_2(B_160,A_159)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_931,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_926])).

tff(c_935,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_882,c_931])).

tff(c_936,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_935])).

tff(c_980,plain,(
    ! [A_171,B_172] :
      ( m1_subset_1('#skF_1'(A_171,B_172),k1_zfmisc_1(u1_struct_0(A_171)))
      | v3_tex_2(B_172,A_171)
      | ~ v2_tex_2(B_172,A_171)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    ! [B_25,A_23] :
      ( v1_zfmisc_1(B_25)
      | ~ v2_tex_2(B_25,A_23)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | v1_xboole_0(B_25)
      | ~ l1_pre_topc(A_23)
      | ~ v2_tdlat_3(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1191,plain,(
    ! [A_202,B_203] :
      ( v1_zfmisc_1('#skF_1'(A_202,B_203))
      | ~ v2_tex_2('#skF_1'(A_202,B_203),A_202)
      | v1_xboole_0('#skF_1'(A_202,B_203))
      | ~ v2_tdlat_3(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202)
      | v3_tex_2(B_203,A_202)
      | ~ v2_tex_2(B_203,A_202)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(resolution,[status(thm)],[c_980,c_32])).

tff(c_1197,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_936,c_1191])).

tff(c_1202,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_882,c_42,c_40,c_1197])).

tff(c_1204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_44,c_913,c_914,c_1202])).

tff(c_1206,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1205,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1606,plain,(
    ! [B_264,A_265] :
      ( v2_tex_2(B_264,A_265)
      | ~ v3_tex_2(B_264,A_265)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(u1_struct_0(A_265)))
      | ~ l1_pre_topc(A_265) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1613,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1606])).

tff(c_1617,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1205,c_1613])).

tff(c_1802,plain,(
    ! [B_298,A_299] :
      ( v1_zfmisc_1(B_298)
      | ~ v2_tex_2(B_298,A_299)
      | ~ m1_subset_1(B_298,k1_zfmisc_1(u1_struct_0(A_299)))
      | v1_xboole_0(B_298)
      | ~ l1_pre_topc(A_299)
      | ~ v2_tdlat_3(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1812,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1802])).

tff(c_1817,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_1617,c_1812])).

tff(c_1819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_36,c_1206,c_1817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.62  
% 3.63/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.62  %$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.63/1.62  
% 3.63/1.62  %Foreground sorts:
% 3.63/1.62  
% 3.63/1.62  
% 3.63/1.62  %Background operators:
% 3.63/1.62  
% 3.63/1.62  
% 3.63/1.62  %Foreground operators:
% 3.63/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.63/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.62  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.63/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.63/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.62  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.63/1.62  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.63/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.63/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.63/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.63/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.62  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.63/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.63/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.63/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.63/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.63/1.62  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.63/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.63/1.62  
% 3.97/1.64  tff(f_125, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 3.97/1.64  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.97/1.64  tff(f_105, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.97/1.64  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.97/1.64  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.97/1.64  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 3.97/1.64  tff(f_61, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.97/1.64  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.97/1.64  tff(c_36, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.97/1.64  tff(c_52, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.97/1.64  tff(c_54, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 3.97/1.64  tff(c_46, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.97/1.64  tff(c_56, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46])).
% 3.97/1.64  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.97/1.64  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.97/1.64  tff(c_794, plain, (![A_135, B_136]: ('#skF_1'(A_135, B_136)!=B_136 | v3_tex_2(B_136, A_135) | ~v2_tex_2(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.97/1.64  tff(c_801, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_794])).
% 3.97/1.64  tff(c_805, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_801])).
% 3.97/1.64  tff(c_806, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_805])).
% 3.97/1.64  tff(c_807, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_806])).
% 3.97/1.64  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.97/1.64  tff(c_40, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.97/1.64  tff(c_867, plain, (![B_151, A_152]: (v2_tex_2(B_151, A_152) | ~v1_zfmisc_1(B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_152))) | v1_xboole_0(B_151) | ~l1_pre_topc(A_152) | ~v2_tdlat_3(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.97/1.64  tff(c_874, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_867])).
% 3.97/1.64  tff(c_878, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_54, c_874])).
% 3.97/1.64  tff(c_880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_807, c_878])).
% 3.97/1.64  tff(c_881, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_806])).
% 3.97/1.64  tff(c_882, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_806])).
% 3.97/1.64  tff(c_891, plain, (![B_155, A_156]: (r1_tarski(B_155, '#skF_1'(A_156, B_155)) | v3_tex_2(B_155, A_156) | ~v2_tex_2(B_155, A_156) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_156))) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.97/1.64  tff(c_896, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_891])).
% 3.97/1.64  tff(c_900, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_882, c_896])).
% 3.97/1.64  tff(c_901, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_900])).
% 3.97/1.64  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.97/1.64  tff(c_91, plain, (![B_37, A_38]: (v1_subset_1(B_37, A_38) | B_37=A_38 | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.97/1.64  tff(c_98, plain, (![A_5, B_6]: (v1_subset_1(A_5, B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_8, c_91])).
% 3.97/1.64  tff(c_81, plain, (![B_35, A_36]: (~v1_subset_1(B_35, A_36) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.97/1.64  tff(c_736, plain, (![A_123, B_124]: (~v1_subset_1(A_123, B_124) | ~v1_xboole_0(B_124) | ~r1_tarski(A_123, B_124))), inference(resolution, [status(thm)], [c_8, c_81])).
% 3.97/1.64  tff(c_743, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_98, c_736])).
% 3.97/1.64  tff(c_907, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | '#skF_1'('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_901, c_743])).
% 3.97/1.64  tff(c_913, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_881, c_907])).
% 3.97/1.64  tff(c_747, plain, (![B_125, A_126]: (~v1_subset_1(B_125, A_126) | v1_xboole_0(B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(A_126)) | ~v1_zfmisc_1(A_126) | v1_xboole_0(A_126))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.97/1.64  tff(c_769, plain, (![A_129, B_130]: (~v1_subset_1(A_129, B_130) | v1_xboole_0(A_129) | ~v1_zfmisc_1(B_130) | v1_xboole_0(B_130) | ~r1_tarski(A_129, B_130))), inference(resolution, [status(thm)], [c_8, c_747])).
% 3.97/1.64  tff(c_776, plain, (![A_5, B_6]: (v1_xboole_0(A_5) | ~v1_zfmisc_1(B_6) | v1_xboole_0(B_6) | B_6=A_5 | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_98, c_769])).
% 3.97/1.64  tff(c_904, plain, (v1_xboole_0('#skF_3') | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | '#skF_1'('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_901, c_776])).
% 3.97/1.64  tff(c_910, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_881, c_36, c_904])).
% 3.97/1.64  tff(c_914, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_913, c_910])).
% 3.97/1.64  tff(c_926, plain, (![A_159, B_160]: (v2_tex_2('#skF_1'(A_159, B_160), A_159) | v3_tex_2(B_160, A_159) | ~v2_tex_2(B_160, A_159) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.97/1.64  tff(c_931, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_926])).
% 3.97/1.64  tff(c_935, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_882, c_931])).
% 3.97/1.64  tff(c_936, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_935])).
% 3.97/1.64  tff(c_980, plain, (![A_171, B_172]: (m1_subset_1('#skF_1'(A_171, B_172), k1_zfmisc_1(u1_struct_0(A_171))) | v3_tex_2(B_172, A_171) | ~v2_tex_2(B_172, A_171) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.97/1.64  tff(c_32, plain, (![B_25, A_23]: (v1_zfmisc_1(B_25) | ~v2_tex_2(B_25, A_23) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | v1_xboole_0(B_25) | ~l1_pre_topc(A_23) | ~v2_tdlat_3(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.97/1.64  tff(c_1191, plain, (![A_202, B_203]: (v1_zfmisc_1('#skF_1'(A_202, B_203)) | ~v2_tex_2('#skF_1'(A_202, B_203), A_202) | v1_xboole_0('#skF_1'(A_202, B_203)) | ~v2_tdlat_3(A_202) | ~v2_pre_topc(A_202) | v2_struct_0(A_202) | v3_tex_2(B_203, A_202) | ~v2_tex_2(B_203, A_202) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(resolution, [status(thm)], [c_980, c_32])).
% 3.97/1.64  tff(c_1197, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_936, c_1191])).
% 3.97/1.64  tff(c_1202, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_882, c_42, c_40, c_1197])).
% 3.97/1.64  tff(c_1204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_44, c_913, c_914, c_1202])).
% 3.97/1.64  tff(c_1206, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 3.97/1.64  tff(c_1205, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 3.97/1.64  tff(c_1606, plain, (![B_264, A_265]: (v2_tex_2(B_264, A_265) | ~v3_tex_2(B_264, A_265) | ~m1_subset_1(B_264, k1_zfmisc_1(u1_struct_0(A_265))) | ~l1_pre_topc(A_265))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.97/1.64  tff(c_1613, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_1606])).
% 3.97/1.64  tff(c_1617, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1205, c_1613])).
% 3.97/1.64  tff(c_1802, plain, (![B_298, A_299]: (v1_zfmisc_1(B_298) | ~v2_tex_2(B_298, A_299) | ~m1_subset_1(B_298, k1_zfmisc_1(u1_struct_0(A_299))) | v1_xboole_0(B_298) | ~l1_pre_topc(A_299) | ~v2_tdlat_3(A_299) | ~v2_pre_topc(A_299) | v2_struct_0(A_299))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.97/1.64  tff(c_1812, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_1802])).
% 3.97/1.64  tff(c_1817, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_1617, c_1812])).
% 3.97/1.64  tff(c_1819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_36, c_1206, c_1817])).
% 3.97/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.64  
% 3.97/1.64  Inference rules
% 3.97/1.64  ----------------------
% 3.97/1.64  #Ref     : 0
% 3.97/1.64  #Sup     : 334
% 3.97/1.64  #Fact    : 0
% 3.97/1.64  #Define  : 0
% 3.97/1.64  #Split   : 8
% 3.97/1.64  #Chain   : 0
% 3.97/1.64  #Close   : 0
% 3.97/1.64  
% 3.97/1.64  Ordering : KBO
% 3.97/1.64  
% 3.97/1.64  Simplification rules
% 3.97/1.64  ----------------------
% 3.97/1.64  #Subsume      : 91
% 3.97/1.64  #Demod        : 198
% 3.97/1.64  #Tautology    : 42
% 3.97/1.64  #SimpNegUnit  : 67
% 3.97/1.64  #BackRed      : 6
% 3.97/1.64  
% 3.97/1.64  #Partial instantiations: 0
% 3.97/1.64  #Strategies tried      : 1
% 3.97/1.64  
% 3.97/1.64  Timing (in seconds)
% 3.97/1.64  ----------------------
% 3.97/1.64  Preprocessing        : 0.29
% 3.97/1.64  Parsing              : 0.16
% 3.97/1.64  CNF conversion       : 0.02
% 3.97/1.64  Main loop            : 0.58
% 3.97/1.64  Inferencing          : 0.23
% 3.97/1.64  Reduction            : 0.15
% 3.97/1.64  Demodulation         : 0.09
% 3.97/1.64  BG Simplification    : 0.02
% 3.97/1.64  Subsumption          : 0.13
% 3.97/1.64  Abstraction          : 0.03
% 3.97/1.64  MUC search           : 0.00
% 3.97/1.64  Cooper               : 0.00
% 3.97/1.64  Total                : 0.91
% 3.97/1.64  Index Insertion      : 0.00
% 3.97/1.64  Index Deletion       : 0.00
% 3.97/1.64  Index Matching       : 0.00
% 3.97/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
