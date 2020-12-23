%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:14 EST 2020

% Result     : Theorem 10.01s
% Output     : CNFRefutation 10.25s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 404 expanded)
%              Number of leaves         :   45 ( 152 expanded)
%              Depth                    :   15
%              Number of atoms          :  275 (1348 expanded)
%              Number of equality atoms :   31 ( 104 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_169,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_40,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_36,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_117,axiom,(
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

tff(f_149,axiom,(
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

tff(f_130,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_76,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_93,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_34,plain,(
    ! [A_23] : m1_subset_1('#skF_3'(A_23),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_177,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(A_71,B_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_191,plain,(
    ! [B_73] : r1_tarski('#skF_3'(k1_zfmisc_1(B_73)),B_73) ),
    inference(resolution,[status(thm)],[c_34,c_177])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_196,plain,(
    '#skF_3'(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_191,c_10])).

tff(c_190,plain,(
    ! [B_72] : r1_tarski('#skF_3'(k1_zfmisc_1(B_72)),B_72) ),
    inference(resolution,[status(thm)],[c_34,c_177])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_236,plain,(
    ! [A_78,C_79,B_80] :
      ( r1_tarski(A_78,k2_xboole_0(C_79,B_80))
      | ~ r1_tarski(A_78,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_258,plain,(
    ! [A_84,A_85] :
      ( r1_tarski(A_84,A_85)
      | ~ r1_tarski(A_84,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_236])).

tff(c_263,plain,(
    ! [A_85] : r1_tarski('#skF_3'(k1_zfmisc_1(k1_xboole_0)),A_85) ),
    inference(resolution,[status(thm)],[c_190,c_258])).

tff(c_266,plain,(
    ! [A_85] : r1_tarski(k1_xboole_0,A_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_263])).

tff(c_76,plain,
    ( ~ v1_zfmisc_1('#skF_7')
    | ~ v3_tex_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_94,plain,(
    ~ v3_tex_2('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_30,plain,(
    ! [A_20] :
      ( v1_zfmisc_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_829,plain,(
    ! [A_145,B_146] :
      ( '#skF_5'(A_145,B_146) != B_146
      | v3_tex_2(B_146,A_145)
      | ~ v2_tex_2(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_840,plain,
    ( '#skF_5'('#skF_6','#skF_7') != '#skF_7'
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_829])).

tff(c_849,plain,
    ( '#skF_5'('#skF_6','#skF_7') != '#skF_7'
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_840])).

tff(c_850,plain,
    ( '#skF_5'('#skF_6','#skF_7') != '#skF_7'
    | ~ v2_tex_2('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_849])).

tff(c_852,plain,(
    ~ v2_tex_2('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_850])).

tff(c_72,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_70,plain,(
    v2_tdlat_3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_82,plain,
    ( v3_tex_2('#skF_7','#skF_6')
    | v1_zfmisc_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_102,plain,(
    v1_zfmisc_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_82])).

tff(c_1041,plain,(
    ! [B_168,A_169] :
      ( v2_tex_2(B_168,A_169)
      | ~ v1_zfmisc_1(B_168)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | v1_xboole_0(B_168)
      | ~ l1_pre_topc(A_169)
      | ~ v2_tdlat_3(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1052,plain,
    ( v2_tex_2('#skF_7','#skF_6')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1041])).

tff(c_1062,plain,
    ( v2_tex_2('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_102,c_1052])).

tff(c_1064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_852,c_1062])).

tff(c_1065,plain,(
    '#skF_5'('#skF_6','#skF_7') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_850])).

tff(c_1066,plain,(
    v2_tex_2('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_850])).

tff(c_1173,plain,(
    ! [B_181,A_182] :
      ( r1_tarski(B_181,'#skF_5'(A_182,B_181))
      | v3_tex_2(B_181,A_182)
      | ~ v2_tex_2(B_181,A_182)
      | ~ m1_subset_1(B_181,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1181,plain,
    ( r1_tarski('#skF_7','#skF_5'('#skF_6','#skF_7'))
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1173])).

tff(c_1190,plain,
    ( r1_tarski('#skF_7','#skF_5'('#skF_6','#skF_7'))
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1066,c_1181])).

tff(c_1191,plain,(
    r1_tarski('#skF_7','#skF_5'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1190])).

tff(c_58,plain,(
    ! [B_42,A_40] :
      ( B_42 = A_40
      | ~ r1_tarski(A_40,B_42)
      | ~ v1_zfmisc_1(B_42)
      | v1_xboole_0(B_42)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1199,plain,
    ( '#skF_5'('#skF_6','#skF_7') = '#skF_7'
    | ~ v1_zfmisc_1('#skF_5'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_5'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1191,c_58])).

tff(c_1206,plain,
    ( ~ v1_zfmisc_1('#skF_5'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_5'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1065,c_1199])).

tff(c_1207,plain,(
    ~ v1_zfmisc_1('#skF_5'('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1206])).

tff(c_1211,plain,(
    ~ v1_xboole_0('#skF_5'('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_30,c_1207])).

tff(c_1125,plain,(
    ! [A_174,B_175] :
      ( v2_tex_2('#skF_5'(A_174,B_175),A_174)
      | v3_tex_2(B_175,A_174)
      | ~ v2_tex_2(B_175,A_174)
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1133,plain,
    ( v2_tex_2('#skF_5'('#skF_6','#skF_7'),'#skF_6')
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1125])).

tff(c_1141,plain,
    ( v2_tex_2('#skF_5'('#skF_6','#skF_7'),'#skF_6')
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1066,c_1133])).

tff(c_1142,plain,(
    v2_tex_2('#skF_5'('#skF_6','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1141])).

tff(c_1276,plain,(
    ! [A_189,B_190] :
      ( m1_subset_1('#skF_5'(A_189,B_190),k1_zfmisc_1(u1_struct_0(A_189)))
      | v3_tex_2(B_190,A_189)
      | ~ v2_tex_2(B_190,A_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    ! [B_45,A_43] :
      ( v1_zfmisc_1(B_45)
      | ~ v2_tex_2(B_45,A_43)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_43)))
      | v1_xboole_0(B_45)
      | ~ l1_pre_topc(A_43)
      | ~ v2_tdlat_3(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_11264,plain,(
    ! [A_501,B_502] :
      ( v1_zfmisc_1('#skF_5'(A_501,B_502))
      | ~ v2_tex_2('#skF_5'(A_501,B_502),A_501)
      | v1_xboole_0('#skF_5'(A_501,B_502))
      | ~ v2_tdlat_3(A_501)
      | ~ v2_pre_topc(A_501)
      | v2_struct_0(A_501)
      | v3_tex_2(B_502,A_501)
      | ~ v2_tex_2(B_502,A_501)
      | ~ m1_subset_1(B_502,k1_zfmisc_1(u1_struct_0(A_501)))
      | ~ l1_pre_topc(A_501) ) ),
    inference(resolution,[status(thm)],[c_1276,c_62])).

tff(c_11272,plain,
    ( v1_zfmisc_1('#skF_5'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_5'('#skF_6','#skF_7'))
    | ~ v2_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_1142,c_11264])).

tff(c_11280,plain,
    ( v1_zfmisc_1('#skF_5'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_5'('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6')
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1066,c_72,c_70,c_11272])).

tff(c_11282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_74,c_1211,c_1207,c_11280])).

tff(c_11283,plain,(
    v1_xboole_0('#skF_5'('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1206])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_104,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_107,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_2,c_104])).

tff(c_11290,plain,(
    '#skF_5'('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11283,c_107])).

tff(c_96,plain,(
    ! [A_51,B_52] : k2_xboole_0(k1_tarski(A_51),B_52) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_100,plain,(
    ! [A_51] : k1_tarski(A_51) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_96])).

tff(c_42,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_4'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_115,plain,(
    ! [C_59,A_60] :
      ( C_59 = A_60
      | ~ r2_hidden(C_59,k1_tarski(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_119,plain,(
    ! [A_60] :
      ( '#skF_4'(k1_tarski(A_60)) = A_60
      | k1_tarski(A_60) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_115])).

tff(c_125,plain,(
    ! [A_60] : '#skF_4'(k1_tarski(A_60)) = A_60 ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_119])).

tff(c_143,plain,(
    ! [A_64] :
      ( r1_xboole_0('#skF_4'(A_64),A_64)
      | k1_xboole_0 = A_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_148,plain,(
    ! [A_60] :
      ( r1_xboole_0(A_60,k1_tarski(A_60))
      | k1_tarski(A_60) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_143])).

tff(c_151,plain,(
    ! [A_65] : r1_xboole_0(A_65,k1_tarski(A_65)) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_148])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_154,plain,(
    ! [A_65] : r1_xboole_0(k1_tarski(A_65),A_65) ),
    inference(resolution,[status(thm)],[c_151,c_4])).

tff(c_245,plain,(
    ! [A_81,C_82,B_83] :
      ( r1_xboole_0(A_81,C_82)
      | ~ r1_xboole_0(B_83,C_82)
      | ~ r1_tarski(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_298,plain,(
    ! [A_89,A_90] :
      ( r1_xboole_0(A_89,A_90)
      | ~ r1_tarski(A_89,k1_tarski(A_90)) ) ),
    inference(resolution,[status(thm)],[c_154,c_245])).

tff(c_310,plain,(
    ! [A_93] : r1_xboole_0(k1_xboole_0,A_93) ),
    inference(resolution,[status(thm)],[c_266,c_298])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_xboole_0(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_380,plain,(
    ! [A_99,A_100] :
      ( r1_xboole_0(A_99,A_100)
      | ~ r1_tarski(A_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_310,c_12])).

tff(c_403,plain,(
    ! [A_102,A_103] :
      ( r1_xboole_0(A_102,A_103)
      | ~ r1_tarski(A_103,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_380,c_4])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ r1_xboole_0(B_12,A_11)
      | ~ r1_tarski(B_12,A_11)
      | v1_xboole_0(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_412,plain,(
    ! [A_102,A_103] :
      ( ~ r1_tarski(A_102,A_103)
      | v1_xboole_0(A_102)
      | ~ r1_tarski(A_103,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_403,c_14])).

tff(c_1196,plain,
    ( v1_xboole_0('#skF_7')
    | ~ r1_tarski('#skF_5'('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1191,c_412])).

tff(c_1203,plain,(
    ~ r1_tarski('#skF_5'('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1196])).

tff(c_11294,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11290,c_1203])).

tff(c_11301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_11294])).

tff(c_11302,plain,(
    ~ v1_zfmisc_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_11303,plain,(
    v3_tex_2('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_11783,plain,(
    ! [B_573,A_574] :
      ( v2_tex_2(B_573,A_574)
      | ~ v3_tex_2(B_573,A_574)
      | ~ m1_subset_1(B_573,k1_zfmisc_1(u1_struct_0(A_574)))
      | ~ l1_pre_topc(A_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_11794,plain,
    ( v2_tex_2('#skF_7','#skF_6')
    | ~ v3_tex_2('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_11783])).

tff(c_11803,plain,(
    v2_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_11303,c_11794])).

tff(c_12357,plain,(
    ! [B_632,A_633] :
      ( v1_zfmisc_1(B_632)
      | ~ v2_tex_2(B_632,A_633)
      | ~ m1_subset_1(B_632,k1_zfmisc_1(u1_struct_0(A_633)))
      | v1_xboole_0(B_632)
      | ~ l1_pre_topc(A_633)
      | ~ v2_tdlat_3(A_633)
      | ~ v2_pre_topc(A_633)
      | v2_struct_0(A_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_12371,plain,
    ( v1_zfmisc_1('#skF_7')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_12357])).

tff(c_12382,plain,
    ( v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_11803,c_12371])).

tff(c_12384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_66,c_11302,c_12382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.01/3.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/3.59  
% 10.01/3.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.25/3.60  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5
% 10.25/3.60  
% 10.25/3.60  %Foreground sorts:
% 10.25/3.60  
% 10.25/3.60  
% 10.25/3.60  %Background operators:
% 10.25/3.60  
% 10.25/3.60  
% 10.25/3.60  %Foreground operators:
% 10.25/3.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.25/3.60  tff('#skF_4', type, '#skF_4': $i > $i).
% 10.25/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.25/3.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.25/3.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.25/3.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.25/3.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.25/3.60  tff('#skF_7', type, '#skF_7': $i).
% 10.25/3.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.25/3.60  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 10.25/3.60  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 10.25/3.60  tff('#skF_6', type, '#skF_6': $i).
% 10.25/3.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.25/3.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.25/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.25/3.60  tff('#skF_3', type, '#skF_3': $i > $i).
% 10.25/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.25/3.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.25/3.60  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 10.25/3.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.25/3.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.25/3.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.25/3.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.25/3.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.25/3.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.25/3.60  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 10.25/3.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.25/3.60  
% 10.25/3.62  tff(f_169, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 10.25/3.62  tff(f_79, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 10.25/3.62  tff(f_83, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.25/3.62  tff(f_40, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 10.25/3.62  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 10.25/3.62  tff(f_34, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 10.25/3.62  tff(f_73, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 10.25/3.62  tff(f_117, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 10.25/3.62  tff(f_149, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 10.25/3.62  tff(f_130, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 10.25/3.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.25/3.62  tff(f_62, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 10.25/3.62  tff(f_76, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 10.25/3.62  tff(f_93, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 10.25/3.62  tff(f_69, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 10.25/3.62  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.25/3.62  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 10.25/3.62  tff(f_54, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 10.25/3.62  tff(c_74, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_169])).
% 10.25/3.62  tff(c_66, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_169])).
% 10.25/3.62  tff(c_34, plain, (![A_23]: (m1_subset_1('#skF_3'(A_23), A_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.25/3.62  tff(c_177, plain, (![A_71, B_72]: (r1_tarski(A_71, B_72) | ~m1_subset_1(A_71, k1_zfmisc_1(B_72)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.25/3.62  tff(c_191, plain, (![B_73]: (r1_tarski('#skF_3'(k1_zfmisc_1(B_73)), B_73))), inference(resolution, [status(thm)], [c_34, c_177])).
% 10.25/3.62  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.25/3.62  tff(c_196, plain, ('#skF_3'(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_191, c_10])).
% 10.25/3.62  tff(c_190, plain, (![B_72]: (r1_tarski('#skF_3'(k1_zfmisc_1(B_72)), B_72))), inference(resolution, [status(thm)], [c_34, c_177])).
% 10.25/3.62  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.25/3.62  tff(c_236, plain, (![A_78, C_79, B_80]: (r1_tarski(A_78, k2_xboole_0(C_79, B_80)) | ~r1_tarski(A_78, B_80))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.25/3.62  tff(c_258, plain, (![A_84, A_85]: (r1_tarski(A_84, A_85) | ~r1_tarski(A_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_236])).
% 10.25/3.62  tff(c_263, plain, (![A_85]: (r1_tarski('#skF_3'(k1_zfmisc_1(k1_xboole_0)), A_85))), inference(resolution, [status(thm)], [c_190, c_258])).
% 10.25/3.62  tff(c_266, plain, (![A_85]: (r1_tarski(k1_xboole_0, A_85))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_263])).
% 10.25/3.62  tff(c_76, plain, (~v1_zfmisc_1('#skF_7') | ~v3_tex_2('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_169])).
% 10.25/3.62  tff(c_94, plain, (~v3_tex_2('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_76])).
% 10.25/3.62  tff(c_30, plain, (![A_20]: (v1_zfmisc_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.25/3.62  tff(c_68, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_169])).
% 10.25/3.62  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 10.25/3.62  tff(c_829, plain, (![A_145, B_146]: ('#skF_5'(A_145, B_146)!=B_146 | v3_tex_2(B_146, A_145) | ~v2_tex_2(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.25/3.62  tff(c_840, plain, ('#skF_5'('#skF_6', '#skF_7')!='#skF_7' | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_829])).
% 10.25/3.62  tff(c_849, plain, ('#skF_5'('#skF_6', '#skF_7')!='#skF_7' | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_840])).
% 10.25/3.62  tff(c_850, plain, ('#skF_5'('#skF_6', '#skF_7')!='#skF_7' | ~v2_tex_2('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_94, c_849])).
% 10.25/3.62  tff(c_852, plain, (~v2_tex_2('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_850])).
% 10.25/3.62  tff(c_72, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_169])).
% 10.25/3.62  tff(c_70, plain, (v2_tdlat_3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_169])).
% 10.25/3.62  tff(c_82, plain, (v3_tex_2('#skF_7', '#skF_6') | v1_zfmisc_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_169])).
% 10.25/3.62  tff(c_102, plain, (v1_zfmisc_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_94, c_82])).
% 10.25/3.62  tff(c_1041, plain, (![B_168, A_169]: (v2_tex_2(B_168, A_169) | ~v1_zfmisc_1(B_168) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_169))) | v1_xboole_0(B_168) | ~l1_pre_topc(A_169) | ~v2_tdlat_3(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.25/3.62  tff(c_1052, plain, (v2_tex_2('#skF_7', '#skF_6') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_64, c_1041])).
% 10.25/3.62  tff(c_1062, plain, (v2_tex_2('#skF_7', '#skF_6') | v1_xboole_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_102, c_1052])).
% 10.25/3.62  tff(c_1064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_852, c_1062])).
% 10.25/3.62  tff(c_1065, plain, ('#skF_5'('#skF_6', '#skF_7')!='#skF_7'), inference(splitRight, [status(thm)], [c_850])).
% 10.25/3.62  tff(c_1066, plain, (v2_tex_2('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_850])).
% 10.25/3.62  tff(c_1173, plain, (![B_181, A_182]: (r1_tarski(B_181, '#skF_5'(A_182, B_181)) | v3_tex_2(B_181, A_182) | ~v2_tex_2(B_181, A_182) | ~m1_subset_1(B_181, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.25/3.62  tff(c_1181, plain, (r1_tarski('#skF_7', '#skF_5'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_1173])).
% 10.25/3.62  tff(c_1190, plain, (r1_tarski('#skF_7', '#skF_5'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1066, c_1181])).
% 10.25/3.62  tff(c_1191, plain, (r1_tarski('#skF_7', '#skF_5'('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_94, c_1190])).
% 10.25/3.62  tff(c_58, plain, (![B_42, A_40]: (B_42=A_40 | ~r1_tarski(A_40, B_42) | ~v1_zfmisc_1(B_42) | v1_xboole_0(B_42) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.25/3.62  tff(c_1199, plain, ('#skF_5'('#skF_6', '#skF_7')='#skF_7' | ~v1_zfmisc_1('#skF_5'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_5'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_1191, c_58])).
% 10.25/3.62  tff(c_1206, plain, (~v1_zfmisc_1('#skF_5'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_5'('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_66, c_1065, c_1199])).
% 10.25/3.62  tff(c_1207, plain, (~v1_zfmisc_1('#skF_5'('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_1206])).
% 10.25/3.62  tff(c_1211, plain, (~v1_xboole_0('#skF_5'('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_1207])).
% 10.25/3.62  tff(c_1125, plain, (![A_174, B_175]: (v2_tex_2('#skF_5'(A_174, B_175), A_174) | v3_tex_2(B_175, A_174) | ~v2_tex_2(B_175, A_174) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.25/3.62  tff(c_1133, plain, (v2_tex_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6') | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_1125])).
% 10.25/3.62  tff(c_1141, plain, (v2_tex_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6') | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1066, c_1133])).
% 10.25/3.62  tff(c_1142, plain, (v2_tex_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_94, c_1141])).
% 10.25/3.62  tff(c_1276, plain, (![A_189, B_190]: (m1_subset_1('#skF_5'(A_189, B_190), k1_zfmisc_1(u1_struct_0(A_189))) | v3_tex_2(B_190, A_189) | ~v2_tex_2(B_190, A_189) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.25/3.62  tff(c_62, plain, (![B_45, A_43]: (v1_zfmisc_1(B_45) | ~v2_tex_2(B_45, A_43) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_43))) | v1_xboole_0(B_45) | ~l1_pre_topc(A_43) | ~v2_tdlat_3(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.25/3.62  tff(c_11264, plain, (![A_501, B_502]: (v1_zfmisc_1('#skF_5'(A_501, B_502)) | ~v2_tex_2('#skF_5'(A_501, B_502), A_501) | v1_xboole_0('#skF_5'(A_501, B_502)) | ~v2_tdlat_3(A_501) | ~v2_pre_topc(A_501) | v2_struct_0(A_501) | v3_tex_2(B_502, A_501) | ~v2_tex_2(B_502, A_501) | ~m1_subset_1(B_502, k1_zfmisc_1(u1_struct_0(A_501))) | ~l1_pre_topc(A_501))), inference(resolution, [status(thm)], [c_1276, c_62])).
% 10.25/3.62  tff(c_11272, plain, (v1_zfmisc_1('#skF_5'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_5'('#skF_6', '#skF_7')) | ~v2_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_1142, c_11264])).
% 10.25/3.62  tff(c_11280, plain, (v1_zfmisc_1('#skF_5'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_5'('#skF_6', '#skF_7')) | v2_struct_0('#skF_6') | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1066, c_72, c_70, c_11272])).
% 10.25/3.62  tff(c_11282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_74, c_1211, c_1207, c_11280])).
% 10.25/3.62  tff(c_11283, plain, (v1_xboole_0('#skF_5'('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_1206])).
% 10.25/3.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.25/3.62  tff(c_104, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.25/3.62  tff(c_107, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_2, c_104])).
% 10.25/3.62  tff(c_11290, plain, ('#skF_5'('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_11283, c_107])).
% 10.25/3.62  tff(c_96, plain, (![A_51, B_52]: (k2_xboole_0(k1_tarski(A_51), B_52)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.25/3.62  tff(c_100, plain, (![A_51]: (k1_tarski(A_51)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_96])).
% 10.25/3.62  tff(c_42, plain, (![A_27]: (r2_hidden('#skF_4'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.25/3.62  tff(c_115, plain, (![C_59, A_60]: (C_59=A_60 | ~r2_hidden(C_59, k1_tarski(A_60)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.25/3.62  tff(c_119, plain, (![A_60]: ('#skF_4'(k1_tarski(A_60))=A_60 | k1_tarski(A_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_115])).
% 10.25/3.62  tff(c_125, plain, (![A_60]: ('#skF_4'(k1_tarski(A_60))=A_60)), inference(negUnitSimplification, [status(thm)], [c_100, c_119])).
% 10.25/3.62  tff(c_143, plain, (![A_64]: (r1_xboole_0('#skF_4'(A_64), A_64) | k1_xboole_0=A_64)), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.25/3.62  tff(c_148, plain, (![A_60]: (r1_xboole_0(A_60, k1_tarski(A_60)) | k1_tarski(A_60)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_143])).
% 10.25/3.62  tff(c_151, plain, (![A_65]: (r1_xboole_0(A_65, k1_tarski(A_65)))), inference(negUnitSimplification, [status(thm)], [c_100, c_148])).
% 10.25/3.62  tff(c_4, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 10.25/3.62  tff(c_154, plain, (![A_65]: (r1_xboole_0(k1_tarski(A_65), A_65))), inference(resolution, [status(thm)], [c_151, c_4])).
% 10.25/3.62  tff(c_245, plain, (![A_81, C_82, B_83]: (r1_xboole_0(A_81, C_82) | ~r1_xboole_0(B_83, C_82) | ~r1_tarski(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.25/3.62  tff(c_298, plain, (![A_89, A_90]: (r1_xboole_0(A_89, A_90) | ~r1_tarski(A_89, k1_tarski(A_90)))), inference(resolution, [status(thm)], [c_154, c_245])).
% 10.25/3.62  tff(c_310, plain, (![A_93]: (r1_xboole_0(k1_xboole_0, A_93))), inference(resolution, [status(thm)], [c_266, c_298])).
% 10.25/3.62  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_xboole_0(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.25/3.62  tff(c_380, plain, (![A_99, A_100]: (r1_xboole_0(A_99, A_100) | ~r1_tarski(A_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_310, c_12])).
% 10.25/3.62  tff(c_403, plain, (![A_102, A_103]: (r1_xboole_0(A_102, A_103) | ~r1_tarski(A_103, k1_xboole_0))), inference(resolution, [status(thm)], [c_380, c_4])).
% 10.25/3.62  tff(c_14, plain, (![B_12, A_11]: (~r1_xboole_0(B_12, A_11) | ~r1_tarski(B_12, A_11) | v1_xboole_0(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.25/3.62  tff(c_412, plain, (![A_102, A_103]: (~r1_tarski(A_102, A_103) | v1_xboole_0(A_102) | ~r1_tarski(A_103, k1_xboole_0))), inference(resolution, [status(thm)], [c_403, c_14])).
% 10.25/3.62  tff(c_1196, plain, (v1_xboole_0('#skF_7') | ~r1_tarski('#skF_5'('#skF_6', '#skF_7'), k1_xboole_0)), inference(resolution, [status(thm)], [c_1191, c_412])).
% 10.25/3.62  tff(c_1203, plain, (~r1_tarski('#skF_5'('#skF_6', '#skF_7'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_66, c_1196])).
% 10.25/3.62  tff(c_11294, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_11290, c_1203])).
% 10.25/3.62  tff(c_11301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_266, c_11294])).
% 10.25/3.62  tff(c_11302, plain, (~v1_zfmisc_1('#skF_7')), inference(splitRight, [status(thm)], [c_76])).
% 10.25/3.62  tff(c_11303, plain, (v3_tex_2('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_76])).
% 10.25/3.62  tff(c_11783, plain, (![B_573, A_574]: (v2_tex_2(B_573, A_574) | ~v3_tex_2(B_573, A_574) | ~m1_subset_1(B_573, k1_zfmisc_1(u1_struct_0(A_574))) | ~l1_pre_topc(A_574))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.25/3.62  tff(c_11794, plain, (v2_tex_2('#skF_7', '#skF_6') | ~v3_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_11783])).
% 10.25/3.62  tff(c_11803, plain, (v2_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_11303, c_11794])).
% 10.25/3.62  tff(c_12357, plain, (![B_632, A_633]: (v1_zfmisc_1(B_632) | ~v2_tex_2(B_632, A_633) | ~m1_subset_1(B_632, k1_zfmisc_1(u1_struct_0(A_633))) | v1_xboole_0(B_632) | ~l1_pre_topc(A_633) | ~v2_tdlat_3(A_633) | ~v2_pre_topc(A_633) | v2_struct_0(A_633))), inference(cnfTransformation, [status(thm)], [f_149])).
% 10.25/3.62  tff(c_12371, plain, (v1_zfmisc_1('#skF_7') | ~v2_tex_2('#skF_7', '#skF_6') | v1_xboole_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_64, c_12357])).
% 10.25/3.62  tff(c_12382, plain, (v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_11803, c_12371])).
% 10.25/3.62  tff(c_12384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_66, c_11302, c_12382])).
% 10.25/3.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.25/3.62  
% 10.25/3.62  Inference rules
% 10.25/3.62  ----------------------
% 10.25/3.62  #Ref     : 0
% 10.25/3.62  #Sup     : 3057
% 10.25/3.62  #Fact    : 2
% 10.25/3.62  #Define  : 0
% 10.25/3.62  #Split   : 12
% 10.25/3.62  #Chain   : 0
% 10.25/3.62  #Close   : 0
% 10.25/3.62  
% 10.25/3.62  Ordering : KBO
% 10.25/3.62  
% 10.25/3.62  Simplification rules
% 10.25/3.62  ----------------------
% 10.25/3.62  #Subsume      : 1406
% 10.25/3.62  #Demod        : 1341
% 10.25/3.62  #Tautology    : 866
% 10.25/3.62  #SimpNegUnit  : 161
% 10.25/3.62  #BackRed      : 6
% 10.25/3.62  
% 10.25/3.62  #Partial instantiations: 0
% 10.25/3.62  #Strategies tried      : 1
% 10.25/3.62  
% 10.25/3.62  Timing (in seconds)
% 10.25/3.62  ----------------------
% 10.25/3.62  Preprocessing        : 0.39
% 10.25/3.62  Parsing              : 0.20
% 10.25/3.62  CNF conversion       : 0.03
% 10.25/3.62  Main loop            : 2.36
% 10.25/3.62  Inferencing          : 0.66
% 10.25/3.62  Reduction            : 0.78
% 10.25/3.62  Demodulation         : 0.54
% 10.25/3.62  BG Simplification    : 0.06
% 10.25/3.62  Subsumption          : 0.73
% 10.25/3.62  Abstraction          : 0.09
% 10.25/3.62  MUC search           : 0.00
% 10.25/3.62  Cooper               : 0.00
% 10.25/3.62  Total                : 2.80
% 10.25/3.62  Index Insertion      : 0.00
% 10.25/3.62  Index Deletion       : 0.00
% 10.25/3.62  Index Matching       : 0.00
% 10.25/3.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
