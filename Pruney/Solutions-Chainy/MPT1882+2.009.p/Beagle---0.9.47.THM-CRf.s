%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:13 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 398 expanded)
%              Number of leaves         :   33 ( 146 expanded)
%              Depth                    :   13
%              Number of atoms          :  224 (1469 expanded)
%              Number of equality atoms :   31 (  99 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_130,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_110,axiom,(
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

tff(f_91,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_16,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_102,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_94])).

tff(c_181,plain,(
    ! [A_54,B_55,C_56] : k4_xboole_0(k4_xboole_0(A_54,B_55),C_56) = k4_xboole_0(A_54,k2_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_218,plain,(
    ! [B_2,C_56] : k4_xboole_0(B_2,k2_xboole_0(B_2,C_56)) = k4_xboole_0(k1_xboole_0,C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_181])).

tff(c_234,plain,(
    ! [C_56] : k4_xboole_0(k1_xboole_0,C_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_218])).

tff(c_62,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_66,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_56,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_68,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_56])).

tff(c_22,plain,(
    ! [A_14] :
      ( v1_zfmisc_1(A_14)
      | ~ v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_525,plain,(
    ! [A_71,B_72] :
      ( '#skF_1'(A_71,B_72) != B_72
      | v3_tex_2(B_72,A_71)
      | ~ v2_tex_2(B_72,A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_528,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_525])).

tff(c_531,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_528])).

tff(c_532,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_531])).

tff(c_533,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_532])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_50,plain,(
    v2_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1097,plain,(
    ! [B_98,A_99] :
      ( v2_tex_2(B_98,A_99)
      | ~ v1_zfmisc_1(B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | v1_xboole_0(B_98)
      | ~ l1_pre_topc(A_99)
      | ~ v2_tdlat_3(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1100,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1097])).

tff(c_1103,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_66,c_1100])).

tff(c_1105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_46,c_533,c_1103])).

tff(c_1106,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_532])).

tff(c_1107,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_532])).

tff(c_1167,plain,(
    ! [B_102,A_103] :
      ( r1_tarski(B_102,'#skF_1'(A_103,B_102))
      | v3_tex_2(B_102,A_103)
      | ~ v2_tex_2(B_102,A_103)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1169,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1167])).

tff(c_1172,plain,
    ( r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3'))
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1107,c_1169])).

tff(c_1173,plain,(
    r1_tarski('#skF_3','#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1172])).

tff(c_38,plain,(
    ! [B_28,A_26] :
      ( B_28 = A_26
      | ~ r1_tarski(A_26,B_28)
      | ~ v1_zfmisc_1(B_28)
      | v1_xboole_0(B_28)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1176,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1173,c_38])).

tff(c_1187,plain,
    ( ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1106,c_1176])).

tff(c_1223,plain,(
    ~ v1_zfmisc_1('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1187])).

tff(c_1227,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_1223])).

tff(c_1216,plain,(
    ! [A_104,B_105] :
      ( v2_tex_2('#skF_1'(A_104,B_105),A_104)
      | v3_tex_2(B_105,A_104)
      | ~ v2_tex_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1218,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1216])).

tff(c_1221,plain,
    ( v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1107,c_1218])).

tff(c_1222,plain,(
    v2_tex_2('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1221])).

tff(c_32,plain,(
    ! [A_16,B_22] :
      ( m1_subset_1('#skF_1'(A_16,B_22),k1_zfmisc_1(u1_struct_0(A_16)))
      | v3_tex_2(B_22,A_16)
      | ~ v2_tex_2(B_22,A_16)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1782,plain,(
    ! [B_125,A_126] :
      ( v1_zfmisc_1(B_125)
      | ~ v2_tex_2(B_125,A_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | v1_xboole_0(B_125)
      | ~ l1_pre_topc(A_126)
      | ~ v2_tdlat_3(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_6926,plain,(
    ! [A_222,B_223] :
      ( v1_zfmisc_1('#skF_1'(A_222,B_223))
      | ~ v2_tex_2('#skF_1'(A_222,B_223),A_222)
      | v1_xboole_0('#skF_1'(A_222,B_223))
      | ~ v2_tdlat_3(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222)
      | v3_tex_2(B_223,A_222)
      | ~ v2_tex_2(B_223,A_222)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222) ) ),
    inference(resolution,[status(thm)],[c_32,c_1782])).

tff(c_6930,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1222,c_6926])).

tff(c_6934,plain,
    ( v1_zfmisc_1('#skF_1'('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_1'('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1107,c_52,c_50,c_6930])).

tff(c_6936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_54,c_1227,c_1223,c_6934])).

tff(c_6937,plain,(
    v1_xboole_0('#skF_1'('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_76,plain,(
    ! [B_36,A_37] :
      ( ~ v1_xboole_0(B_36)
      | B_36 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_79,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_2,c_76])).

tff(c_6944,plain,(
    '#skF_1'('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6937,c_79])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_110,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_110])).

tff(c_1179,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | k4_xboole_0('#skF_1'('#skF_2','#skF_3'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1173,c_115])).

tff(c_1190,plain,(
    k4_xboole_0('#skF_1'('#skF_2','#skF_3'),'#skF_3') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1106,c_1179])).

tff(c_6950,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6944,c_1190])).

tff(c_6957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_6950])).

tff(c_6959,plain,(
    ~ v1_zfmisc_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6958,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_7395,plain,(
    ! [B_257,A_258] :
      ( v2_tex_2(B_257,A_258)
      | ~ v3_tex_2(B_257,A_258)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7398,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_7395])).

tff(c_7401,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6958,c_7398])).

tff(c_8416,plain,(
    ! [B_295,A_296] :
      ( v1_zfmisc_1(B_295)
      | ~ v2_tex_2(B_295,A_296)
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0(A_296)))
      | v1_xboole_0(B_295)
      | ~ l1_pre_topc(A_296)
      | ~ v2_tdlat_3(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8419,plain,
    ( v1_zfmisc_1('#skF_3')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | v1_xboole_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_8416])).

tff(c_8422,plain,
    ( v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_7401,c_8419])).

tff(c_8424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_46,c_6959,c_8422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.17  
% 5.73/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.18  %$ v3_tex_2 > v2_tex_2 > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.73/2.18  
% 5.73/2.18  %Foreground sorts:
% 5.73/2.18  
% 5.73/2.18  
% 5.73/2.18  %Background operators:
% 5.73/2.18  
% 5.73/2.18  
% 5.73/2.18  %Foreground operators:
% 5.73/2.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.73/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.73/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.73/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.73/2.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.73/2.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.73/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.73/2.18  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 5.73/2.18  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.73/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.73/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.73/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.73/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.73/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.73/2.18  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.73/2.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.73/2.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.73/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.73/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.73/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.73/2.18  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 5.73/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.73/2.18  
% 5.73/2.19  tff(f_130, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tex_2)).
% 5.73/2.19  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.73/2.19  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.73/2.19  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.73/2.19  tff(f_38, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.73/2.19  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 5.73/2.19  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 5.73/2.19  tff(f_110, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 5.73/2.19  tff(f_91, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 5.73/2.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.73/2.19  tff(f_48, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 5.73/2.19  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.73/2.19  tff(c_46, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.73/2.19  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.73/2.19  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.73/2.19  tff(c_94, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.73/2.19  tff(c_102, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_94])).
% 5.73/2.19  tff(c_181, plain, (![A_54, B_55, C_56]: (k4_xboole_0(k4_xboole_0(A_54, B_55), C_56)=k4_xboole_0(A_54, k2_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.73/2.19  tff(c_218, plain, (![B_2, C_56]: (k4_xboole_0(B_2, k2_xboole_0(B_2, C_56))=k4_xboole_0(k1_xboole_0, C_56))), inference(superposition, [status(thm), theory('equality')], [c_102, c_181])).
% 5.73/2.19  tff(c_234, plain, (![C_56]: (k4_xboole_0(k1_xboole_0, C_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_218])).
% 5.73/2.19  tff(c_62, plain, (v3_tex_2('#skF_3', '#skF_2') | v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.73/2.19  tff(c_66, plain, (v1_zfmisc_1('#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 5.73/2.19  tff(c_56, plain, (~v1_zfmisc_1('#skF_3') | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.73/2.19  tff(c_68, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_56])).
% 5.73/2.19  tff(c_22, plain, (![A_14]: (v1_zfmisc_1(A_14) | ~v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.73/2.19  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.73/2.19  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.73/2.19  tff(c_525, plain, (![A_71, B_72]: ('#skF_1'(A_71, B_72)!=B_72 | v3_tex_2(B_72, A_71) | ~v2_tex_2(B_72, A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.73/2.19  tff(c_528, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_525])).
% 5.73/2.19  tff(c_531, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_528])).
% 5.73/2.19  tff(c_532, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | ~v2_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_531])).
% 5.73/2.19  tff(c_533, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_532])).
% 5.73/2.19  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.73/2.19  tff(c_50, plain, (v2_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.73/2.19  tff(c_1097, plain, (![B_98, A_99]: (v2_tex_2(B_98, A_99) | ~v1_zfmisc_1(B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_99))) | v1_xboole_0(B_98) | ~l1_pre_topc(A_99) | ~v2_tdlat_3(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.73/2.19  tff(c_1100, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1097])).
% 5.73/2.19  tff(c_1103, plain, (v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_66, c_1100])).
% 5.73/2.19  tff(c_1105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_46, c_533, c_1103])).
% 5.73/2.19  tff(c_1106, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_532])).
% 5.73/2.19  tff(c_1107, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_532])).
% 5.73/2.19  tff(c_1167, plain, (![B_102, A_103]: (r1_tarski(B_102, '#skF_1'(A_103, B_102)) | v3_tex_2(B_102, A_103) | ~v2_tex_2(B_102, A_103) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.73/2.19  tff(c_1169, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1167])).
% 5.73/2.19  tff(c_1172, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3')) | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1107, c_1169])).
% 5.73/2.19  tff(c_1173, plain, (r1_tarski('#skF_3', '#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1172])).
% 5.73/2.19  tff(c_38, plain, (![B_28, A_26]: (B_28=A_26 | ~r1_tarski(A_26, B_28) | ~v1_zfmisc_1(B_28) | v1_xboole_0(B_28) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.73/2.19  tff(c_1176, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_1173, c_38])).
% 5.73/2.19  tff(c_1187, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_46, c_1106, c_1176])).
% 5.73/2.19  tff(c_1223, plain, (~v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1187])).
% 5.73/2.19  tff(c_1227, plain, (~v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1223])).
% 5.73/2.19  tff(c_1216, plain, (![A_104, B_105]: (v2_tex_2('#skF_1'(A_104, B_105), A_104) | v3_tex_2(B_105, A_104) | ~v2_tex_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.73/2.19  tff(c_1218, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1216])).
% 5.73/2.19  tff(c_1221, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1107, c_1218])).
% 5.73/2.19  tff(c_1222, plain, (v2_tex_2('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_1221])).
% 5.73/2.19  tff(c_32, plain, (![A_16, B_22]: (m1_subset_1('#skF_1'(A_16, B_22), k1_zfmisc_1(u1_struct_0(A_16))) | v3_tex_2(B_22, A_16) | ~v2_tex_2(B_22, A_16) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.73/2.19  tff(c_1782, plain, (![B_125, A_126]: (v1_zfmisc_1(B_125) | ~v2_tex_2(B_125, A_126) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | v1_xboole_0(B_125) | ~l1_pre_topc(A_126) | ~v2_tdlat_3(A_126) | ~v2_pre_topc(A_126) | v2_struct_0(A_126))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.73/2.19  tff(c_6926, plain, (![A_222, B_223]: (v1_zfmisc_1('#skF_1'(A_222, B_223)) | ~v2_tex_2('#skF_1'(A_222, B_223), A_222) | v1_xboole_0('#skF_1'(A_222, B_223)) | ~v2_tdlat_3(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222) | v3_tex_2(B_223, A_222) | ~v2_tex_2(B_223, A_222) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222))), inference(resolution, [status(thm)], [c_32, c_1782])).
% 5.73/2.19  tff(c_6930, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1222, c_6926])).
% 5.73/2.19  tff(c_6934, plain, (v1_zfmisc_1('#skF_1'('#skF_2', '#skF_3')) | v1_xboole_0('#skF_1'('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1107, c_52, c_50, c_6930])).
% 5.73/2.19  tff(c_6936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_54, c_1227, c_1223, c_6934])).
% 5.73/2.19  tff(c_6937, plain, (v1_xboole_0('#skF_1'('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1187])).
% 5.73/2.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.73/2.19  tff(c_76, plain, (![B_36, A_37]: (~v1_xboole_0(B_36) | B_36=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.73/2.19  tff(c_79, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_2, c_76])).
% 5.73/2.19  tff(c_6944, plain, ('#skF_1'('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_6937, c_79])).
% 5.73/2.19  tff(c_10, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.73/2.19  tff(c_110, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.73/2.19  tff(c_115, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_110])).
% 5.73/2.19  tff(c_1179, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | k4_xboole_0('#skF_1'('#skF_2', '#skF_3'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1173, c_115])).
% 5.73/2.19  tff(c_1190, plain, (k4_xboole_0('#skF_1'('#skF_2', '#skF_3'), '#skF_3')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1106, c_1179])).
% 5.73/2.19  tff(c_6950, plain, (k4_xboole_0(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6944, c_1190])).
% 5.73/2.19  tff(c_6957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_234, c_6950])).
% 5.73/2.19  tff(c_6959, plain, (~v1_zfmisc_1('#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 5.73/2.19  tff(c_6958, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 5.73/2.19  tff(c_7395, plain, (![B_257, A_258]: (v2_tex_2(B_257, A_258) | ~v3_tex_2(B_257, A_258) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.73/2.19  tff(c_7398, plain, (v2_tex_2('#skF_3', '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_7395])).
% 5.73/2.19  tff(c_7401, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6958, c_7398])).
% 5.73/2.19  tff(c_8416, plain, (![B_295, A_296]: (v1_zfmisc_1(B_295) | ~v2_tex_2(B_295, A_296) | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0(A_296))) | v1_xboole_0(B_295) | ~l1_pre_topc(A_296) | ~v2_tdlat_3(A_296) | ~v2_pre_topc(A_296) | v2_struct_0(A_296))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.73/2.19  tff(c_8419, plain, (v1_zfmisc_1('#skF_3') | ~v2_tex_2('#skF_3', '#skF_2') | v1_xboole_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_8416])).
% 5.73/2.19  tff(c_8422, plain, (v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_7401, c_8419])).
% 5.73/2.19  tff(c_8424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_46, c_6959, c_8422])).
% 5.73/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.73/2.19  
% 5.73/2.19  Inference rules
% 5.73/2.19  ----------------------
% 5.73/2.19  #Ref     : 0
% 5.73/2.19  #Sup     : 2045
% 5.73/2.19  #Fact    : 2
% 5.73/2.19  #Define  : 0
% 5.73/2.19  #Split   : 5
% 5.73/2.19  #Chain   : 0
% 5.73/2.19  #Close   : 0
% 5.73/2.19  
% 5.73/2.19  Ordering : KBO
% 5.73/2.19  
% 5.73/2.19  Simplification rules
% 5.73/2.19  ----------------------
% 5.73/2.19  #Subsume      : 80
% 5.73/2.19  #Demod        : 1460
% 5.73/2.19  #Tautology    : 1286
% 5.73/2.19  #SimpNegUnit  : 88
% 5.73/2.19  #BackRed      : 26
% 5.73/2.19  
% 5.73/2.19  #Partial instantiations: 0
% 5.73/2.19  #Strategies tried      : 1
% 5.73/2.19  
% 5.73/2.19  Timing (in seconds)
% 5.73/2.19  ----------------------
% 5.73/2.20  Preprocessing        : 0.31
% 5.73/2.20  Parsing              : 0.18
% 5.73/2.20  CNF conversion       : 0.02
% 5.73/2.20  Main loop            : 1.08
% 5.73/2.20  Inferencing          : 0.35
% 5.73/2.20  Reduction            : 0.45
% 5.73/2.20  Demodulation         : 0.36
% 5.73/2.20  BG Simplification    : 0.04
% 5.73/2.20  Subsumption          : 0.17
% 5.73/2.20  Abstraction          : 0.05
% 5.73/2.20  MUC search           : 0.00
% 5.73/2.20  Cooper               : 0.00
% 5.73/2.20  Total                : 1.43
% 5.73/2.20  Index Insertion      : 0.00
% 5.73/2.20  Index Deletion       : 0.00
% 5.73/2.20  Index Matching       : 0.00
% 5.73/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
