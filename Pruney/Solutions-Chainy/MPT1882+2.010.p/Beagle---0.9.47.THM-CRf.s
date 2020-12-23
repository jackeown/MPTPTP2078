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
% DateTime   : Thu Dec  3 10:30:13 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 351 expanded)
%              Number of leaves         :   30 ( 129 expanded)
%              Depth                    :   13
%              Number of atoms          :  228 (1301 expanded)
%              Number of equality atoms :   21 (  92 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_126,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_74,axiom,(
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

tff(f_106,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    ! [A_35,C_36,B_37] :
      ( r1_tarski(A_35,k2_xboole_0(C_36,B_37))
      | ~ r1_tarski(A_35,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_92,plain,(
    ! [A_38,A_39] :
      ( r1_tarski(A_38,A_39)
      | ~ r1_tarski(A_38,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_88])).

tff(c_96,plain,(
    ! [A_39] : r1_tarski(k1_xboole_0,A_39) ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_50,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_69,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_16,plain,(
    ! [A_9] :
      ( v1_zfmisc_1(A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_213,plain,(
    ! [A_65,B_66] :
      ( '#skF_1'(A_65,B_66) != B_66
      | v3_tex_2(B_66,A_65)
      | ~ v2_tex_2(B_66,A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_216,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_213])).

tff(c_219,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_216])).

tff(c_220,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_219])).

tff(c_221,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_70,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_56])).

tff(c_298,plain,(
    ! [B_83,A_84] :
      ( v2_tex_2(B_83,A_84)
      | ~ v1_zfmisc_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | v1_xboole_0(B_83)
      | ~ l1_pre_topc(A_84)
      | ~ v2_tdlat_3(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_304,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_298])).

tff(c_308,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_70,c_304])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_221,c_308])).

tff(c_311,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_312,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_355,plain,(
    ! [B_95,A_96] :
      ( r1_tarski(B_95,'#skF_1'(A_96,B_95))
      | v3_tex_2(B_95,A_96)
      | ~ v2_tex_2(B_95,A_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_357,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_355])).

tff(c_360,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_312,c_357])).

tff(c_361,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_360])).

tff(c_32,plain,(
    ! [B_23,A_21] :
      ( B_23 = A_21
      | ~ r1_tarski(A_21,B_23)
      | ~ v1_zfmisc_1(B_23)
      | v1_xboole_0(B_23)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_366,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_361,c_32])).

tff(c_374,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_311,c_366])).

tff(c_378,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_382,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_378])).

tff(c_326,plain,(
    ! [A_90,B_91] :
      ( v2_tex_2('#skF_1'(A_90,B_91),A_90)
      | v3_tex_2(B_91,A_90)
      | ~ v2_tex_2(B_91,A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_328,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_326])).

tff(c_331,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_312,c_328])).

tff(c_332,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_331])).

tff(c_26,plain,(
    ! [A_11,B_17] :
      ( m1_subset_1('#skF_1'(A_11,B_17),k1_zfmisc_1(u1_struct_0(A_11)))
      | v3_tex_2(B_17,A_11)
      | ~ v2_tex_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_410,plain,(
    ! [B_101,A_102] :
      ( v1_zfmisc_1(B_101)
      | ~ v2_tex_2(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | v1_xboole_0(B_101)
      | ~ l1_pre_topc(A_102)
      | ~ v2_tdlat_3(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_648,plain,(
    ! [A_184,B_185] :
      ( v1_zfmisc_1('#skF_1'(A_184,B_185))
      | ~ v2_tex_2('#skF_1'(A_184,B_185),A_184)
      | v1_xboole_0('#skF_1'(A_184,B_185))
      | ~ v2_tdlat_3(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | v3_tex_2(B_185,A_184)
      | ~ v2_tex_2(B_185,A_184)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ l1_pre_topc(A_184) ) ),
    inference(resolution,[status(thm)],[c_26,c_410])).

tff(c_652,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_332,c_648])).

tff(c_656,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_312,c_46,c_44,c_652])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_48,c_382,c_378,c_656])).

tff(c_659,plain,(
    v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_71,plain,(
    ! [B_31,A_32] :
      ( ~ v1_xboole_0(B_31)
      | B_31 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_666,plain,(
    '#skF_1'('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_659,c_74])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_103,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_144,plain,(
    ! [C_46,B_47,A_48] :
      ( k2_xboole_0(C_46,B_47) = A_48
      | ~ r1_tarski(k2_xboole_0(C_46,B_47),A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(resolution,[status(thm)],[c_10,c_103])).

tff(c_151,plain,(
    ! [A_6,A_48] :
      ( k2_xboole_0(A_6,k1_xboole_0) = A_48
      | ~ r1_tarski(A_6,A_48)
      | ~ r1_tarski(A_48,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_144])).

tff(c_157,plain,(
    ! [A_6,A_48] :
      ( A_6 = A_48
      | ~ r1_tarski(A_6,A_48)
      | ~ r1_tarski(A_48,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_151])).

tff(c_363,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_361,c_157])).

tff(c_371,plain,(
    ~ r1_tarski('#skF_1'('#skF_2','#skF_3'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_363])).

tff(c_674,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_371])).

tff(c_682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_674])).

tff(c_683,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_684,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_791,plain,(
    ! [B_206,A_207] :
      ( v2_tex_2(B_206,A_207)
      | ~ v3_tex_2(B_206,A_207)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_794,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_791])).

tff(c_797,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_684,c_794])).

tff(c_884,plain,(
    ! [B_235,A_236] :
      ( v1_zfmisc_1(B_235)
      | ~ v2_tex_2(B_235,A_236)
      | ~ m1_subset_1(B_235,k1_zfmisc_1(u1_struct_0(A_236)))
      | v1_xboole_0(B_235)
      | ~ l1_pre_topc(A_236)
      | ~ v2_tdlat_3(A_236)
      | ~ v2_pre_topc(A_236)
      | v2_struct_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_890,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_884])).

tff(c_894,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_797,c_890])).

tff(c_896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_40,c_683,c_894])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:12:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.50  
% 3.41/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.50  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.41/1.50  
% 3.41/1.50  %Foreground sorts:
% 3.41/1.50  
% 3.41/1.50  
% 3.41/1.50  %Background operators:
% 3.41/1.50  
% 3.41/1.50  
% 3.41/1.50  %Foreground operators:
% 3.41/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.41/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.41/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.50  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.41/1.50  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.41/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.41/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.50  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.41/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.41/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.41/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.41/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.41/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.41/1.50  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 3.41/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.41/1.50  
% 3.41/1.52  tff(f_126, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 3.41/1.52  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.41/1.52  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.41/1.52  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.41/1.52  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 3.41/1.52  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.41/1.52  tff(f_106, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 3.41/1.52  tff(f_87, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.41/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.41/1.52  tff(f_46, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.41/1.52  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.41/1.52  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.41/1.52  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.41/1.52  tff(c_12, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.41/1.52  tff(c_88, plain, (![A_35, C_36, B_37]: (r1_tarski(A_35, k2_xboole_0(C_36, B_37)) | ~r1_tarski(A_35, B_37))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.41/1.52  tff(c_92, plain, (![A_38, A_39]: (r1_tarski(A_38, A_39) | ~r1_tarski(A_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_88])).
% 3.41/1.52  tff(c_96, plain, (![A_39]: (r1_tarski(k1_xboole_0, A_39))), inference(resolution, [status(thm)], [c_8, c_92])).
% 3.41/1.52  tff(c_50, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.41/1.52  tff(c_69, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 3.41/1.52  tff(c_16, plain, (![A_9]: (v1_zfmisc_1(A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.41/1.52  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.41/1.52  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.41/1.52  tff(c_213, plain, (![A_65, B_66]: ('#skF_1'(A_65, B_66)!=B_66 | v3_tex_2(B_66, A_65) | ~v2_tex_2(B_66, A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.41/1.52  tff(c_216, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_213])).
% 3.41/1.52  tff(c_219, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_216])).
% 3.41/1.52  tff(c_220, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_69, c_219])).
% 3.41/1.52  tff(c_221, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_220])).
% 3.41/1.52  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.41/1.52  tff(c_44, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.41/1.52  tff(c_56, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.41/1.52  tff(c_70, plain, (v1_zfmisc_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_69, c_56])).
% 3.41/1.52  tff(c_298, plain, (![B_83, A_84]: (v2_tex_2(B_83, A_84) | ~v1_zfmisc_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | v1_xboole_0(B_83) | ~l1_pre_topc(A_84) | ~v2_tdlat_3(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.52  tff(c_304, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_298])).
% 3.41/1.52  tff(c_308, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_70, c_304])).
% 3.41/1.52  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_221, c_308])).
% 3.41/1.52  tff(c_311, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_220])).
% 3.41/1.52  tff(c_312, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_220])).
% 3.41/1.52  tff(c_355, plain, (![B_95, A_96]: (r1_tarski(B_95, '#skF_1'(A_96, B_95)) | v3_tex_2(B_95, A_96) | ~v2_tex_2(B_95, A_96) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.41/1.52  tff(c_357, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_355])).
% 3.41/1.52  tff(c_360, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_312, c_357])).
% 3.41/1.52  tff(c_361, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_69, c_360])).
% 3.41/1.52  tff(c_32, plain, (![B_23, A_21]: (B_23=A_21 | ~r1_tarski(A_21, B_23) | ~v1_zfmisc_1(B_23) | v1_xboole_0(B_23) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.41/1.52  tff(c_366, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_361, c_32])).
% 3.41/1.52  tff(c_374, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_40, c_311, c_366])).
% 3.41/1.52  tff(c_378, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_374])).
% 3.41/1.52  tff(c_382, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_378])).
% 3.41/1.52  tff(c_326, plain, (![A_90, B_91]: (v2_tex_2('#skF_1'(A_90, B_91), A_90) | v3_tex_2(B_91, A_90) | ~v2_tex_2(B_91, A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.41/1.52  tff(c_328, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_326])).
% 3.41/1.52  tff(c_331, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_312, c_328])).
% 3.41/1.52  tff(c_332, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_69, c_331])).
% 3.41/1.52  tff(c_26, plain, (![A_11, B_17]: (m1_subset_1('#skF_1'(A_11, B_17), k1_zfmisc_1(u1_struct_0(A_11))) | v3_tex_2(B_17, A_11) | ~v2_tex_2(B_17, A_11) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.41/1.52  tff(c_410, plain, (![B_101, A_102]: (v1_zfmisc_1(B_101) | ~v2_tex_2(B_101, A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | v1_xboole_0(B_101) | ~l1_pre_topc(A_102) | ~v2_tdlat_3(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.52  tff(c_648, plain, (![A_184, B_185]: (v1_zfmisc_1('#skF_1'(A_184, B_185)) | ~v2_tex_2('#skF_1'(A_184, B_185), A_184) | v1_xboole_0('#skF_1'(A_184, B_185)) | ~v2_tdlat_3(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184) | v3_tex_2(B_185, A_184) | ~v2_tex_2(B_185, A_184) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_184))) | ~l1_pre_topc(A_184))), inference(resolution, [status(thm)], [c_26, c_410])).
% 3.41/1.52  tff(c_652, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_332, c_648])).
% 3.41/1.52  tff(c_656, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_312, c_46, c_44, c_652])).
% 3.41/1.52  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_48, c_382, c_378, c_656])).
% 3.41/1.52  tff(c_659, plain, (v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_374])).
% 3.41/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.41/1.52  tff(c_71, plain, (![B_31, A_32]: (~v1_xboole_0(B_31) | B_31=A_32 | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.41/1.52  tff(c_74, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_2, c_71])).
% 3.41/1.52  tff(c_666, plain, ('#skF_1'('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_659, c_74])).
% 3.41/1.52  tff(c_10, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.41/1.52  tff(c_103, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.41/1.52  tff(c_144, plain, (![C_46, B_47, A_48]: (k2_xboole_0(C_46, B_47)=A_48 | ~r1_tarski(k2_xboole_0(C_46, B_47), A_48) | ~r1_tarski(A_48, B_47))), inference(resolution, [status(thm)], [c_10, c_103])).
% 3.41/1.52  tff(c_151, plain, (![A_6, A_48]: (k2_xboole_0(A_6, k1_xboole_0)=A_48 | ~r1_tarski(A_6, A_48) | ~r1_tarski(A_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_144])).
% 3.41/1.52  tff(c_157, plain, (![A_6, A_48]: (A_6=A_48 | ~r1_tarski(A_6, A_48) | ~r1_tarski(A_48, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_151])).
% 3.41/1.52  tff(c_363, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_1'('#skF_2', '#skF_3'), k1_xboole_0)), inference(resolution, [status(thm)], [c_361, c_157])).
% 3.41/1.52  tff(c_371, plain, (~r1_tarski('#skF_1'('#skF_2', '#skF_3'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_311, c_363])).
% 3.41/1.52  tff(c_674, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_666, c_371])).
% 3.41/1.52  tff(c_682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_674])).
% 3.41/1.52  tff(c_683, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.41/1.52  tff(c_684, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 3.41/1.52  tff(c_791, plain, (![B_206, A_207]: (v2_tex_2(B_206, A_207) | ~v3_tex_2(B_206, A_207) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.41/1.52  tff(c_794, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_791])).
% 3.41/1.52  tff(c_797, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_684, c_794])).
% 3.41/1.52  tff(c_884, plain, (![B_235, A_236]: (v1_zfmisc_1(B_235) | ~v2_tex_2(B_235, A_236) | ~m1_subset_1(B_235, k1_zfmisc_1(u1_struct_0(A_236))) | v1_xboole_0(B_235) | ~l1_pre_topc(A_236) | ~v2_tdlat_3(A_236) | ~v2_pre_topc(A_236) | v2_struct_0(A_236))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.41/1.52  tff(c_890, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_884])).
% 3.41/1.52  tff(c_894, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_797, c_890])).
% 3.41/1.52  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_40, c_683, c_894])).
% 3.41/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.52  
% 3.41/1.52  Inference rules
% 3.41/1.52  ----------------------
% 3.41/1.52  #Ref     : 0
% 3.41/1.52  #Sup     : 167
% 3.41/1.52  #Fact    : 0
% 3.41/1.52  #Define  : 0
% 3.41/1.52  #Split   : 5
% 3.41/1.52  #Chain   : 0
% 3.41/1.52  #Close   : 0
% 3.41/1.52  
% 3.41/1.52  Ordering : KBO
% 3.41/1.52  
% 3.41/1.52  Simplification rules
% 3.41/1.52  ----------------------
% 3.41/1.52  #Subsume      : 39
% 3.41/1.52  #Demod        : 124
% 3.41/1.52  #Tautology    : 44
% 3.41/1.52  #SimpNegUnit  : 23
% 3.41/1.52  #BackRed      : 7
% 3.41/1.52  
% 3.41/1.52  #Partial instantiations: 0
% 3.41/1.52  #Strategies tried      : 1
% 3.41/1.52  
% 3.41/1.52  Timing (in seconds)
% 3.41/1.52  ----------------------
% 3.41/1.52  Preprocessing        : 0.30
% 3.41/1.52  Parsing              : 0.17
% 3.41/1.52  CNF conversion       : 0.02
% 3.41/1.52  Main loop            : 0.44
% 3.41/1.52  Inferencing          : 0.16
% 3.41/1.52  Reduction            : 0.12
% 3.41/1.52  Demodulation         : 0.08
% 3.41/1.52  BG Simplification    : 0.02
% 3.41/1.52  Subsumption          : 0.11
% 3.41/1.52  Abstraction          : 0.02
% 3.41/1.52  MUC search           : 0.00
% 3.41/1.52  Cooper               : 0.00
% 3.41/1.52  Total                : 0.78
% 3.41/1.52  Index Insertion      : 0.00
% 3.41/1.52  Index Deletion       : 0.00
% 3.41/1.52  Index Matching       : 0.00
% 3.41/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
