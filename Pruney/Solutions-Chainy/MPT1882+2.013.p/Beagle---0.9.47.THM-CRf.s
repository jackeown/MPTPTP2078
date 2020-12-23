%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:14 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 387 expanded)
%              Number of leaves         :   29 ( 141 expanded)
%              Depth                    :   13
%              Number of atoms          :  210 (1453 expanded)
%              Number of equality atoms :   18 (  85 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_121,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_69,axiom,(
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

tff(f_101,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [B_37] : k4_xboole_0(B_37,B_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_14,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [B_37] : r1_tarski(k1_xboole_0,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_14])).

tff(c_56,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_61,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_64,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_50])).

tff(c_16,plain,(
    ! [A_8] :
      ( v1_zfmisc_1(A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_341,plain,(
    ! [A_62,B_63] :
      ( '#skF_1'(A_62,B_63) != B_63
      | v3_tex_2(B_63,A_62)
      | ~ v2_tex_2(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_344,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_341])).

tff(c_347,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_344])).

tff(c_348,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_347])).

tff(c_349,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_694,plain,(
    ! [B_76,A_77] :
      ( v2_tex_2(B_76,A_77)
      | ~ v1_zfmisc_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_77)))
      | v1_xboole_0(B_76)
      | ~ l1_pre_topc(A_77)
      | ~ v2_tdlat_3(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_697,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_694])).

tff(c_700,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_61,c_697])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_349,c_700])).

tff(c_703,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_704,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_801,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(B_81,'#skF_1'(A_82,B_81))
      | v3_tex_2(B_81,A_82)
      | ~ v2_tex_2(B_81,A_82)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_803,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_801])).

tff(c_806,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_704,c_803])).

tff(c_807,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_806])).

tff(c_32,plain,(
    ! [B_22,A_20] :
      ( B_22 = A_20
      | ~ r1_tarski(A_20,B_22)
      | ~ v1_zfmisc_1(B_22)
      | v1_xboole_0(B_22)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_810,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_807,c_32])).

tff(c_821,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_703,c_810])).

tff(c_833,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_821])).

tff(c_837,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_833])).

tff(c_897,plain,(
    ! [A_83,B_84] :
      ( v2_tex_2('#skF_1'(A_83,B_84),A_83)
      | v3_tex_2(B_84,A_83)
      | ~ v2_tex_2(B_84,A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_899,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_897])).

tff(c_902,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_704,c_899])).

tff(c_903,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_902])).

tff(c_26,plain,(
    ! [A_10,B_16] :
      ( m1_subset_1('#skF_1'(A_10,B_16),k1_zfmisc_1(u1_struct_0(A_10)))
      | v3_tex_2(B_16,A_10)
      | ~ v2_tex_2(B_16,A_10)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1171,plain,(
    ! [B_94,A_95] :
      ( v1_zfmisc_1(B_94)
      | ~ v2_tex_2(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | v1_xboole_0(B_94)
      | ~ l1_pre_topc(A_95)
      | ~ v2_tdlat_3(A_95)
      | ~ v2_pre_topc(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1329,plain,(
    ! [A_120,B_121] :
      ( v1_zfmisc_1('#skF_1'(A_120,B_121))
      | ~ v2_tex_2('#skF_1'(A_120,B_121),A_120)
      | v1_xboole_0('#skF_1'(A_120,B_121))
      | ~ v2_tdlat_3(A_120)
      | ~ v2_pre_topc(A_120)
      | v2_struct_0(A_120)
      | v3_tex_2(B_121,A_120)
      | ~ v2_tex_2(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_26,c_1171])).

tff(c_1333,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_903,c_1329])).

tff(c_1337,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_704,c_46,c_44,c_1333])).

tff(c_1339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_48,c_837,c_833,c_1337])).

tff(c_1340,plain,(
    v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_821])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1345,plain,(
    '#skF_1'('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1340,c_2])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_815,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_807,c_4])).

tff(c_827,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_703,c_815])).

tff(c_1352,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_827])).

tff(c_1358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1352])).

tff(c_1360,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1359,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1619,plain,(
    ! [B_148,A_149] :
      ( v2_tex_2(B_148,A_149)
      | ~ v3_tex_2(B_148,A_149)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1622,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1619])).

tff(c_1625,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1359,c_1622])).

tff(c_1670,plain,(
    ! [B_162,A_163] :
      ( v1_zfmisc_1(B_162)
      | ~ v2_tex_2(B_162,A_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(u1_struct_0(A_163)))
      | v1_xboole_0(B_162)
      | ~ l1_pre_topc(A_163)
      | ~ v2_tdlat_3(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1673,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1670])).

tff(c_1676,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_1625,c_1673])).

tff(c_1678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_1360,c_1676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.57  
% 3.51/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.57  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.51/1.57  
% 3.51/1.57  %Foreground sorts:
% 3.51/1.57  
% 3.51/1.57  
% 3.51/1.57  %Background operators:
% 3.51/1.57  
% 3.51/1.57  
% 3.51/1.57  %Foreground operators:
% 3.51/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.51/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.51/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.51/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.57  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.51/1.57  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.51/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.51/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.57  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.51/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.51/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.51/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.51/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.51/1.57  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.51/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.57  
% 3.51/1.59  tff(f_121, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 3.51/1.59  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.51/1.59  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.51/1.59  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.51/1.59  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 3.51/1.59  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.51/1.59  tff(f_101, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.51/1.59  tff(f_82, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.51/1.59  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.51/1.59  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.51/1.59  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.51/1.59  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.51/1.59  tff(c_72, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.51/1.59  tff(c_86, plain, (![B_37]: (k4_xboole_0(B_37, B_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_72])).
% 3.51/1.59  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.51/1.59  tff(c_91, plain, (![B_37]: (r1_tarski(k1_xboole_0, B_37))), inference(superposition, [status(thm), theory('equality')], [c_86, c_14])).
% 3.51/1.59  tff(c_56, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.51/1.59  tff(c_61, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 3.51/1.59  tff(c_50, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.51/1.59  tff(c_64, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_50])).
% 3.51/1.59  tff(c_16, plain, (![A_8]: (v1_zfmisc_1(A_8) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.51/1.59  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.51/1.59  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.51/1.59  tff(c_341, plain, (![A_62, B_63]: ('#skF_1'(A_62, B_63)!=B_63 | v3_tex_2(B_63, A_62) | ~v2_tex_2(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.51/1.59  tff(c_344, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_341])).
% 3.51/1.59  tff(c_347, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_344])).
% 3.51/1.59  tff(c_348, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_347])).
% 3.51/1.59  tff(c_349, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_348])).
% 3.51/1.59  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.51/1.59  tff(c_44, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.51/1.59  tff(c_694, plain, (![B_76, A_77]: (v2_tex_2(B_76, A_77) | ~v1_zfmisc_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_77))) | v1_xboole_0(B_76) | ~l1_pre_topc(A_77) | ~v2_tdlat_3(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.51/1.59  tff(c_697, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_694])).
% 3.51/1.59  tff(c_700, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_61, c_697])).
% 3.51/1.59  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_349, c_700])).
% 3.51/1.59  tff(c_703, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_348])).
% 3.51/1.59  tff(c_704, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_348])).
% 3.51/1.59  tff(c_801, plain, (![B_81, A_82]: (r1_tarski(B_81, '#skF_1'(A_82, B_81)) | v3_tex_2(B_81, A_82) | ~v2_tex_2(B_81, A_82) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.51/1.59  tff(c_803, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_801])).
% 3.51/1.59  tff(c_806, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_704, c_803])).
% 3.51/1.59  tff(c_807, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_806])).
% 3.51/1.59  tff(c_32, plain, (![B_22, A_20]: (B_22=A_20 | ~r1_tarski(A_20, B_22) | ~v1_zfmisc_1(B_22) | v1_xboole_0(B_22) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.51/1.59  tff(c_810, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_807, c_32])).
% 3.51/1.59  tff(c_821, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_703, c_810])).
% 3.51/1.59  tff(c_833, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_821])).
% 3.51/1.59  tff(c_837, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_833])).
% 3.51/1.59  tff(c_897, plain, (![A_83, B_84]: (v2_tex_2('#skF_1'(A_83, B_84), A_83) | v3_tex_2(B_84, A_83) | ~v2_tex_2(B_84, A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.51/1.59  tff(c_899, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_897])).
% 3.51/1.59  tff(c_902, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_704, c_899])).
% 3.51/1.59  tff(c_903, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_902])).
% 3.51/1.59  tff(c_26, plain, (![A_10, B_16]: (m1_subset_1('#skF_1'(A_10, B_16), k1_zfmisc_1(u1_struct_0(A_10))) | v3_tex_2(B_16, A_10) | ~v2_tex_2(B_16, A_10) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.51/1.59  tff(c_1171, plain, (![B_94, A_95]: (v1_zfmisc_1(B_94) | ~v2_tex_2(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | v1_xboole_0(B_94) | ~l1_pre_topc(A_95) | ~v2_tdlat_3(A_95) | ~v2_pre_topc(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.51/1.59  tff(c_1329, plain, (![A_120, B_121]: (v1_zfmisc_1('#skF_1'(A_120, B_121)) | ~v2_tex_2('#skF_1'(A_120, B_121), A_120) | v1_xboole_0('#skF_1'(A_120, B_121)) | ~v2_tdlat_3(A_120) | ~v2_pre_topc(A_120) | v2_struct_0(A_120) | v3_tex_2(B_121, A_120) | ~v2_tex_2(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_26, c_1171])).
% 3.51/1.59  tff(c_1333, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_903, c_1329])).
% 3.51/1.59  tff(c_1337, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_704, c_46, c_44, c_1333])).
% 3.51/1.59  tff(c_1339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_48, c_837, c_833, c_1337])).
% 3.51/1.59  tff(c_1340, plain, (v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_821])).
% 3.51/1.59  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.51/1.59  tff(c_1345, plain, ('#skF_1'('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1340, c_2])).
% 3.51/1.59  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.51/1.59  tff(c_815, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_807, c_4])).
% 3.51/1.59  tff(c_827, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_703, c_815])).
% 3.51/1.59  tff(c_1352, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1345, c_827])).
% 3.51/1.59  tff(c_1358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_1352])).
% 3.51/1.59  tff(c_1360, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 3.51/1.59  tff(c_1359, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 3.51/1.59  tff(c_1619, plain, (![B_148, A_149]: (v2_tex_2(B_148, A_149) | ~v3_tex_2(B_148, A_149) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.51/1.59  tff(c_1622, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_1619])).
% 3.51/1.59  tff(c_1625, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1359, c_1622])).
% 3.51/1.59  tff(c_1670, plain, (![B_162, A_163]: (v1_zfmisc_1(B_162) | ~v2_tex_2(B_162, A_163) | ~m1_subset_1(B_162, k1_zfmisc_1(u1_struct_0(A_163))) | v1_xboole_0(B_162) | ~l1_pre_topc(A_163) | ~v2_tdlat_3(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.51/1.59  tff(c_1673, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_1670])).
% 3.51/1.59  tff(c_1676, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_1625, c_1673])).
% 3.51/1.59  tff(c_1678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_1360, c_1676])).
% 3.51/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.59  
% 3.51/1.59  Inference rules
% 3.51/1.59  ----------------------
% 3.51/1.59  #Ref     : 0
% 3.51/1.59  #Sup     : 328
% 3.51/1.59  #Fact    : 2
% 3.51/1.59  #Define  : 0
% 3.51/1.59  #Split   : 11
% 3.51/1.59  #Chain   : 0
% 3.51/1.59  #Close   : 0
% 3.51/1.59  
% 3.51/1.59  Ordering : KBO
% 3.51/1.59  
% 3.51/1.59  Simplification rules
% 3.51/1.59  ----------------------
% 3.51/1.59  #Subsume      : 88
% 3.51/1.59  #Demod        : 262
% 3.51/1.59  #Tautology    : 172
% 3.51/1.59  #SimpNegUnit  : 82
% 3.51/1.59  #BackRed      : 6
% 3.51/1.59  
% 3.51/1.59  #Partial instantiations: 0
% 3.51/1.59  #Strategies tried      : 1
% 3.51/1.59  
% 3.51/1.59  Timing (in seconds)
% 3.51/1.59  ----------------------
% 3.51/1.59  Preprocessing        : 0.31
% 3.51/1.59  Parsing              : 0.17
% 3.51/1.59  CNF conversion       : 0.02
% 3.51/1.59  Main loop            : 0.50
% 3.51/1.59  Inferencing          : 0.18
% 3.51/1.59  Reduction            : 0.16
% 3.51/1.59  Demodulation         : 0.11
% 3.51/1.59  BG Simplification    : 0.02
% 3.51/1.59  Subsumption          : 0.10
% 3.51/1.59  Abstraction          : 0.02
% 3.51/1.59  MUC search           : 0.00
% 3.51/1.59  Cooper               : 0.00
% 3.51/1.59  Total                : 0.86
% 3.51/1.59  Index Insertion      : 0.00
% 3.51/1.59  Index Deletion       : 0.00
% 3.51/1.59  Index Matching       : 0.00
% 3.51/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
