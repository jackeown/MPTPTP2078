%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:34 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 165 expanded)
%              Number of leaves         :   37 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 362 expanded)
%              Number of equality atoms :   31 (  73 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_107,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & v1_tops_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_48,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_46,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_44,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_51,plain,(
    ! [A_60] :
      ( k1_xboole_0 = A_60
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_10,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_61,plain,(
    ! [A_8] : m1_subset_1('#skF_6',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_10])).

tff(c_129,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k1_tops_1(A_83,B_84),B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_137,plain,(
    ! [A_85] :
      ( r1_tarski(k1_tops_1(A_85,'#skF_6'),'#skF_6')
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_61,c_129])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_4] :
      ( A_4 = '#skF_6'
      | ~ r1_tarski(A_4,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_6])).

tff(c_150,plain,(
    ! [A_88] :
      ( k1_tops_1(A_88,'#skF_6') = '#skF_6'
      | ~ l1_pre_topc(A_88) ) ),
    inference(resolution,[status(thm)],[c_137,c_71])).

tff(c_157,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_150])).

tff(c_142,plain,(
    ! [A_86,B_87] :
      ( r1_tarski('#skF_4'(A_86,B_87),B_87)
      | v2_tex_2(B_87,A_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_191,plain,(
    ! [A_92] :
      ( r1_tarski('#skF_4'(A_92,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_61,c_142])).

tff(c_196,plain,(
    ! [A_93] :
      ( '#skF_4'(A_93,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_191,c_71])).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_199,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_196,c_40])).

tff(c_202,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_199])).

tff(c_20,plain,(
    ! [A_14] :
      ( m1_subset_1('#skF_2'(A_14),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [C_31,A_19,D_33,B_27] :
      ( v3_pre_topc(C_31,A_19)
      | k1_tops_1(A_19,C_31) != C_31
      | ~ m1_subset_1(D_33,k1_zfmisc_1(u1_struct_0(B_27)))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(B_27)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_229,plain,(
    ! [D_96,B_97] :
      ( ~ m1_subset_1(D_96,k1_zfmisc_1(u1_struct_0(B_97)))
      | ~ l1_pre_topc(B_97) ) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_236,plain,(
    ! [A_14] : ~ l1_pre_topc(A_14) ),
    inference(resolution,[status(thm)],[c_20,c_229])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_46])).

tff(c_281,plain,(
    ! [C_105,A_106] :
      ( v3_pre_topc(C_105,A_106)
      | k1_tops_1(A_106,C_105) != C_105
      | ~ m1_subset_1(C_105,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_294,plain,(
    ! [A_106] :
      ( v3_pre_topc('#skF_6',A_106)
      | k1_tops_1(A_106,'#skF_6') != '#skF_6'
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_61,c_281])).

tff(c_4,plain,(
    ! [A_2,B_3] : r1_tarski(k3_xboole_0(A_2,B_3),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_65] :
      ( A_65 = '#skF_6'
      | ~ r1_tarski(A_65,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_6])).

tff(c_77,plain,(
    ! [B_3] : k3_xboole_0('#skF_6',B_3) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_111,plain,(
    ! [A_74,B_75,C_76] :
      ( k9_subset_1(A_74,B_75,C_76) = k3_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_117,plain,(
    ! [A_8,B_75] : k9_subset_1(A_8,B_75,'#skF_6') = k3_xboole_0(B_75,'#skF_6') ),
    inference(resolution,[status(thm)],[c_61,c_111])).

tff(c_374,plain,(
    ! [A_126,B_127,D_128] :
      ( k9_subset_1(u1_struct_0(A_126),B_127,D_128) != '#skF_4'(A_126,B_127)
      | ~ v3_pre_topc(D_128,A_126)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(u1_struct_0(A_126)))
      | v2_tex_2(B_127,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_379,plain,(
    ! [B_75,A_126] :
      ( k3_xboole_0(B_75,'#skF_6') != '#skF_4'(A_126,B_75)
      | ~ v3_pre_topc('#skF_6',A_126)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_126)))
      | v2_tex_2(B_75,A_126)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_374])).

tff(c_382,plain,(
    ! [B_129,A_130] :
      ( k3_xboole_0(B_129,'#skF_6') != '#skF_4'(A_130,B_129)
      | ~ v3_pre_topc('#skF_6',A_130)
      | v2_tex_2(B_129,A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ l1_pre_topc(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_379])).

tff(c_395,plain,(
    ! [A_130] :
      ( k3_xboole_0('#skF_6','#skF_6') != '#skF_4'(A_130,'#skF_6')
      | ~ v3_pre_topc('#skF_6',A_130)
      | v2_tex_2('#skF_6',A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_61,c_382])).

tff(c_401,plain,(
    ! [A_131] :
      ( '#skF_4'(A_131,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_131)
      | v2_tex_2('#skF_6',A_131)
      | ~ l1_pre_topc(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_395])).

tff(c_406,plain,(
    ! [A_132] :
      ( '#skF_4'(A_132,'#skF_6') != '#skF_6'
      | v2_tex_2('#skF_6',A_132)
      | k1_tops_1(A_132,'#skF_6') != '#skF_6'
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_294,c_401])).

tff(c_409,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | k1_tops_1('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_406,c_40])).

tff(c_413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_157,c_202,c_409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:04:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.40  
% 2.60/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.40  %$ v3_pre_topc > v2_tex_2 > v1_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_1 > #skF_3 > #skF_4
% 2.60/1.40  
% 2.60/1.40  %Foreground sorts:
% 2.60/1.40  
% 2.60/1.40  
% 2.60/1.40  %Background operators:
% 2.60/1.40  
% 2.60/1.40  
% 2.60/1.40  %Foreground operators:
% 2.60/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.60/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.60/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.60/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.60/1.40  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.60/1.40  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.60/1.40  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.60/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.60/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.60/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.60/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.60/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.60/1.40  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.60/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.60/1.40  
% 2.60/1.42  tff(f_122, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.60/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.60/1.42  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.60/1.42  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 2.60/1.42  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.60/1.42  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 2.60/1.42  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v1_tops_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_tops_1)).
% 2.60/1.42  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 2.60/1.42  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.60/1.42  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.60/1.42  tff(c_48, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.60/1.42  tff(c_46, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.60/1.42  tff(c_44, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.60/1.42  tff(c_51, plain, (![A_60]: (k1_xboole_0=A_60 | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.42  tff(c_55, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_44, c_51])).
% 2.60/1.42  tff(c_10, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.60/1.42  tff(c_61, plain, (![A_8]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_10])).
% 2.60/1.42  tff(c_129, plain, (![A_83, B_84]: (r1_tarski(k1_tops_1(A_83, B_84), B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.60/1.42  tff(c_137, plain, (![A_85]: (r1_tarski(k1_tops_1(A_85, '#skF_6'), '#skF_6') | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_61, c_129])).
% 2.60/1.42  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.42  tff(c_71, plain, (![A_4]: (A_4='#skF_6' | ~r1_tarski(A_4, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_6])).
% 2.60/1.42  tff(c_150, plain, (![A_88]: (k1_tops_1(A_88, '#skF_6')='#skF_6' | ~l1_pre_topc(A_88))), inference(resolution, [status(thm)], [c_137, c_71])).
% 2.60/1.42  tff(c_157, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_150])).
% 2.60/1.42  tff(c_142, plain, (![A_86, B_87]: (r1_tarski('#skF_4'(A_86, B_87), B_87) | v2_tex_2(B_87, A_86) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.60/1.42  tff(c_191, plain, (![A_92]: (r1_tarski('#skF_4'(A_92, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_61, c_142])).
% 2.60/1.42  tff(c_196, plain, (![A_93]: ('#skF_4'(A_93, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_93) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_191, c_71])).
% 2.60/1.42  tff(c_40, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.60/1.42  tff(c_199, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_196, c_40])).
% 2.60/1.42  tff(c_202, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_199])).
% 2.60/1.42  tff(c_20, plain, (![A_14]: (m1_subset_1('#skF_2'(A_14), k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.60/1.42  tff(c_24, plain, (![C_31, A_19, D_33, B_27]: (v3_pre_topc(C_31, A_19) | k1_tops_1(A_19, C_31)!=C_31 | ~m1_subset_1(D_33, k1_zfmisc_1(u1_struct_0(B_27))) | ~m1_subset_1(C_31, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(B_27) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.60/1.42  tff(c_229, plain, (![D_96, B_97]: (~m1_subset_1(D_96, k1_zfmisc_1(u1_struct_0(B_97))) | ~l1_pre_topc(B_97))), inference(splitLeft, [status(thm)], [c_24])).
% 2.60/1.42  tff(c_236, plain, (![A_14]: (~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_20, c_229])).
% 2.60/1.42  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_46])).
% 2.60/1.42  tff(c_281, plain, (![C_105, A_106]: (v3_pre_topc(C_105, A_106) | k1_tops_1(A_106, C_105)!=C_105 | ~m1_subset_1(C_105, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106))), inference(splitRight, [status(thm)], [c_24])).
% 2.60/1.42  tff(c_294, plain, (![A_106]: (v3_pre_topc('#skF_6', A_106) | k1_tops_1(A_106, '#skF_6')!='#skF_6' | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106))), inference(resolution, [status(thm)], [c_61, c_281])).
% 2.60/1.42  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(k3_xboole_0(A_2, B_3), A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.42  tff(c_72, plain, (![A_65]: (A_65='#skF_6' | ~r1_tarski(A_65, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_6])).
% 2.60/1.42  tff(c_77, plain, (![B_3]: (k3_xboole_0('#skF_6', B_3)='#skF_6')), inference(resolution, [status(thm)], [c_4, c_72])).
% 2.60/1.42  tff(c_111, plain, (![A_74, B_75, C_76]: (k9_subset_1(A_74, B_75, C_76)=k3_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.42  tff(c_117, plain, (![A_8, B_75]: (k9_subset_1(A_8, B_75, '#skF_6')=k3_xboole_0(B_75, '#skF_6'))), inference(resolution, [status(thm)], [c_61, c_111])).
% 2.60/1.42  tff(c_374, plain, (![A_126, B_127, D_128]: (k9_subset_1(u1_struct_0(A_126), B_127, D_128)!='#skF_4'(A_126, B_127) | ~v3_pre_topc(D_128, A_126) | ~m1_subset_1(D_128, k1_zfmisc_1(u1_struct_0(A_126))) | v2_tex_2(B_127, A_126) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.60/1.42  tff(c_379, plain, (![B_75, A_126]: (k3_xboole_0(B_75, '#skF_6')!='#skF_4'(A_126, B_75) | ~v3_pre_topc('#skF_6', A_126) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_126))) | v2_tex_2(B_75, A_126) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(superposition, [status(thm), theory('equality')], [c_117, c_374])).
% 2.60/1.42  tff(c_382, plain, (![B_129, A_130]: (k3_xboole_0(B_129, '#skF_6')!='#skF_4'(A_130, B_129) | ~v3_pre_topc('#skF_6', A_130) | v2_tex_2(B_129, A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~l1_pre_topc(A_130))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_379])).
% 2.60/1.42  tff(c_395, plain, (![A_130]: (k3_xboole_0('#skF_6', '#skF_6')!='#skF_4'(A_130, '#skF_6') | ~v3_pre_topc('#skF_6', A_130) | v2_tex_2('#skF_6', A_130) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_61, c_382])).
% 2.60/1.42  tff(c_401, plain, (![A_131]: ('#skF_4'(A_131, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_131) | v2_tex_2('#skF_6', A_131) | ~l1_pre_topc(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_395])).
% 2.60/1.42  tff(c_406, plain, (![A_132]: ('#skF_4'(A_132, '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', A_132) | k1_tops_1(A_132, '#skF_6')!='#skF_6' | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132))), inference(resolution, [status(thm)], [c_294, c_401])).
% 2.60/1.42  tff(c_409, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | k1_tops_1('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_406, c_40])).
% 2.60/1.42  tff(c_413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_157, c_202, c_409])).
% 2.60/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.42  
% 2.60/1.42  Inference rules
% 2.60/1.42  ----------------------
% 2.60/1.42  #Ref     : 0
% 2.60/1.42  #Sup     : 80
% 2.60/1.42  #Fact    : 0
% 2.60/1.42  #Define  : 0
% 2.60/1.42  #Split   : 2
% 2.60/1.42  #Chain   : 0
% 2.60/1.42  #Close   : 0
% 2.60/1.42  
% 2.60/1.42  Ordering : KBO
% 2.60/1.42  
% 2.60/1.42  Simplification rules
% 2.60/1.42  ----------------------
% 2.60/1.42  #Subsume      : 18
% 2.60/1.42  #Demod        : 35
% 2.60/1.42  #Tautology    : 26
% 2.60/1.42  #SimpNegUnit  : 7
% 2.60/1.42  #BackRed      : 3
% 2.60/1.42  
% 2.60/1.42  #Partial instantiations: 0
% 2.60/1.42  #Strategies tried      : 1
% 2.60/1.42  
% 2.60/1.42  Timing (in seconds)
% 2.60/1.42  ----------------------
% 2.60/1.42  Preprocessing        : 0.35
% 2.60/1.42  Parsing              : 0.19
% 2.60/1.42  CNF conversion       : 0.03
% 2.60/1.42  Main loop            : 0.27
% 2.60/1.42  Inferencing          : 0.11
% 2.60/1.42  Reduction            : 0.08
% 2.60/1.42  Demodulation         : 0.05
% 2.60/1.42  BG Simplification    : 0.02
% 2.60/1.42  Subsumption          : 0.04
% 2.60/1.42  Abstraction          : 0.02
% 2.60/1.42  MUC search           : 0.00
% 2.60/1.42  Cooper               : 0.00
% 2.60/1.42  Total                : 0.65
% 2.60/1.42  Index Insertion      : 0.00
% 2.60/1.42  Index Deletion       : 0.00
% 2.60/1.42  Index Matching       : 0.00
% 2.60/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
