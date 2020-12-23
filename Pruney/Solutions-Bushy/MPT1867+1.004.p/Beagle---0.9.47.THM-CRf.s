%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1867+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:35 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 276 expanded)
%              Number of leaves         :   34 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          :  150 ( 610 expanded)
%              Number of equality atoms :   29 ( 115 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_80,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_71,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    ! [A_50] :
      ( k1_xboole_0 = A_50
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_50])).

tff(c_26,plain,(
    ! [A_40] : v1_xboole_0('#skF_4'(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_60,plain,(
    ! [A_40] : '#skF_4'(A_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_50])).

tff(c_79,plain,(
    ! [A_40] : '#skF_4'(A_40) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60])).

tff(c_28,plain,(
    ! [A_40] : m1_subset_1('#skF_4'(A_40),k1_zfmisc_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_90,plain,(
    ! [A_40] : m1_subset_1('#skF_6',k1_zfmisc_1(A_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_28])).

tff(c_394,plain,(
    ! [A_95,B_96] :
      ( r1_tarski('#skF_2'(A_95,B_96),B_96)
      | v2_tex_2(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_407,plain,(
    ! [A_97] :
      ( r1_tarski('#skF_2'(A_97,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_90,c_394])).

tff(c_34,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(A_45,k1_zfmisc_1(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_116,plain,(
    ! [B_61,A_62] :
      ( v1_xboole_0(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [A_45,B_46] :
      ( v1_xboole_0(A_45)
      | ~ v1_xboole_0(B_46)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_34,c_116])).

tff(c_412,plain,(
    ! [A_97] :
      ( v1_xboole_0('#skF_2'(A_97,'#skF_6'))
      | ~ v1_xboole_0('#skF_6')
      | v2_tex_2('#skF_6',A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_407,c_127])).

tff(c_417,plain,(
    ! [A_98] :
      ( v1_xboole_0('#skF_2'(A_98,'#skF_6'))
      | v2_tex_2('#skF_6',A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_412])).

tff(c_36,plain,(
    ! [A_47] :
      ( k1_xboole_0 = A_47
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_69,plain,(
    ! [A_47] :
      ( A_47 = '#skF_6'
      | ~ v1_xboole_0(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_36])).

tff(c_422,plain,(
    ! [A_99] :
      ( '#skF_2'(A_99,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_417,c_69])).

tff(c_425,plain,
    ( '#skF_2'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_422,c_38])).

tff(c_428,plain,(
    '#skF_2'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_425])).

tff(c_46,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_486,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1('#skF_2'(A_104,B_105),k1_zfmisc_1(u1_struct_0(A_104)))
      | v2_tex_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( v3_pre_topc(B_6,A_4)
      | ~ v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4)
      | ~ v2_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1012,plain,(
    ! [A_151,B_152] :
      ( v3_pre_topc('#skF_2'(A_151,B_152),A_151)
      | ~ v1_xboole_0('#skF_2'(A_151,B_152))
      | ~ v2_pre_topc(A_151)
      | v2_tex_2(B_152,A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_486,c_4])).

tff(c_1031,plain,(
    ! [A_153] :
      ( v3_pre_topc('#skF_2'(A_153,'#skF_6'),A_153)
      | ~ v1_xboole_0('#skF_2'(A_153,'#skF_6'))
      | ~ v2_pre_topc(A_153)
      | v2_tex_2('#skF_6',A_153)
      | ~ l1_pre_topc(A_153) ) ),
    inference(resolution,[status(thm)],[c_90,c_1012])).

tff(c_1034,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ v1_xboole_0('#skF_2'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_5')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_1031])).

tff(c_1036,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_42,c_428,c_1034])).

tff(c_1037,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1036])).

tff(c_189,plain,(
    ! [A_72,B_73,C_74] :
      ( k9_subset_1(A_72,B_73,C_74) = k3_xboole_0(B_73,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_200,plain,(
    ! [A_75,B_76] : k9_subset_1(A_75,B_76,'#skF_6') = k3_xboole_0(B_76,'#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_189])).

tff(c_22,plain,(
    ! [A_35] : m1_subset_1('#skF_3'(A_35),A_35) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_167,plain,(
    ! [A_67,B_68,C_69] :
      ( k9_subset_1(A_67,B_68,B_68) = B_68
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_176,plain,(
    ! [A_67,B_68] : k9_subset_1(A_67,B_68,B_68) = B_68 ),
    inference(resolution,[status(thm)],[c_22,c_167])).

tff(c_207,plain,(
    k3_xboole_0('#skF_6','#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_176])).

tff(c_198,plain,(
    ! [A_40,B_73] : k9_subset_1(A_40,B_73,'#skF_6') = k3_xboole_0(B_73,'#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_189])).

tff(c_251,plain,(
    ! [A_82,C_83,B_84] :
      ( k9_subset_1(A_82,C_83,B_84) = k9_subset_1(A_82,B_84,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_255,plain,(
    ! [A_40,B_84] : k9_subset_1(A_40,B_84,'#skF_6') = k9_subset_1(A_40,'#skF_6',B_84) ),
    inference(resolution,[status(thm)],[c_90,c_251])).

tff(c_261,plain,(
    ! [A_40,B_84] : k9_subset_1(A_40,'#skF_6',B_84) = k3_xboole_0(B_84,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_255])).

tff(c_704,plain,(
    ! [A_126,B_127,D_128] :
      ( k9_subset_1(u1_struct_0(A_126),B_127,D_128) != '#skF_2'(A_126,B_127)
      | ~ v3_pre_topc(D_128,A_126)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(u1_struct_0(A_126)))
      | v2_tex_2(B_127,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_710,plain,(
    ! [B_84,A_126] :
      ( k3_xboole_0(B_84,'#skF_6') != '#skF_2'(A_126,'#skF_6')
      | ~ v3_pre_topc(B_84,A_126)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_126)))
      | v2_tex_2('#skF_6',A_126)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_704])).

tff(c_1266,plain,(
    ! [B_168,A_169] :
      ( k3_xboole_0(B_168,'#skF_6') != '#skF_2'(A_169,'#skF_6')
      | ~ v3_pre_topc(B_168,A_169)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_169)))
      | v2_tex_2('#skF_6',A_169)
      | ~ l1_pre_topc(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_710])).

tff(c_1280,plain,(
    ! [A_169] :
      ( k3_xboole_0('#skF_6','#skF_6') != '#skF_2'(A_169,'#skF_6')
      | ~ v3_pre_topc('#skF_6',A_169)
      | v2_tex_2('#skF_6',A_169)
      | ~ l1_pre_topc(A_169) ) ),
    inference(resolution,[status(thm)],[c_90,c_1266])).

tff(c_1292,plain,(
    ! [A_170] :
      ( '#skF_2'(A_170,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_170)
      | v2_tex_2('#skF_6',A_170)
      | ~ l1_pre_topc(A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_1280])).

tff(c_1295,plain,
    ( '#skF_2'('#skF_5','#skF_6') != '#skF_6'
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1037,c_1292])).

tff(c_1301,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_428,c_1295])).

tff(c_1303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1301])).

%------------------------------------------------------------------------------
