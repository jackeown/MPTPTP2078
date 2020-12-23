%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:26 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 195 expanded)
%              Number of leaves         :   36 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  137 ( 459 expanded)
%              Number of equality atoms :   29 (  71 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_101,axiom,(
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
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_50,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_56,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_54,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_71,plain,(
    ! [A_58] :
      ( k1_xboole_0 = A_58
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54,c_71])).

tff(c_32,plain,(
    ! [A_22] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_82,plain,(
    ! [A_22] : m1_subset_1('#skF_6',k1_zfmisc_1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_32])).

tff(c_533,plain,(
    ! [A_114,B_115] :
      ( r1_tarski('#skF_4'(A_114,B_115),B_115)
      | v2_tex_2(B_115,A_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_547,plain,(
    ! [A_116] :
      ( r1_tarski('#skF_4'(A_116,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_82,c_533])).

tff(c_251,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_2'(A_72,B_73),A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_255,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_251,c_4])).

tff(c_259,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_264,plain,(
    ! [B_73,A_72] :
      ( B_73 = A_72
      | ~ r1_tarski(B_73,A_72)
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_255,c_259])).

tff(c_553,plain,(
    ! [A_116] :
      ( '#skF_4'(A_116,'#skF_6') = '#skF_6'
      | ~ v1_xboole_0('#skF_6')
      | v2_tex_2('#skF_6',A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_547,c_264])).

tff(c_571,plain,(
    ! [A_118] :
      ( '#skF_4'(A_118,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_553])).

tff(c_574,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_571,c_50])).

tff(c_577,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_574])).

tff(c_58,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_594,plain,(
    ! [A_119,B_120] :
      ( m1_subset_1('#skF_4'(A_119,B_120),k1_zfmisc_1(u1_struct_0(A_119)))
      | v2_tex_2(B_120,A_119)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    ! [B_28,A_26] :
      ( v4_pre_topc(B_28,A_26)
      | ~ v1_xboole_0(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1336,plain,(
    ! [A_178,B_179] :
      ( v4_pre_topc('#skF_4'(A_178,B_179),A_178)
      | ~ v1_xboole_0('#skF_4'(A_178,B_179))
      | ~ v2_pre_topc(A_178)
      | v2_tex_2(B_179,A_178)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_594,c_36])).

tff(c_1352,plain,(
    ! [A_180] :
      ( v4_pre_topc('#skF_4'(A_180,'#skF_6'),A_180)
      | ~ v1_xboole_0('#skF_4'(A_180,'#skF_6'))
      | ~ v2_pre_topc(A_180)
      | v2_tex_2('#skF_6',A_180)
      | ~ l1_pre_topc(A_180) ) ),
    inference(resolution,[status(thm)],[c_82,c_1336])).

tff(c_1355,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ v1_xboole_0('#skF_4'('#skF_5','#skF_6'))
    | ~ v2_pre_topc('#skF_5')
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_1352])).

tff(c_1357,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_54,c_577,c_1355])).

tff(c_1358,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1357])).

tff(c_164,plain,(
    ! [A_68,B_69] : k4_xboole_0(A_68,k4_xboole_0(A_68,B_69)) = k3_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_18] : k4_xboole_0(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_83,plain,(
    ! [A_18] : k4_xboole_0('#skF_6',A_18) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_28])).

tff(c_194,plain,(
    ! [B_70] : k3_xboole_0('#skF_6',B_70) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_83])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_199,plain,(
    ! [B_70] : k3_xboole_0(B_70,'#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_2])).

tff(c_377,plain,(
    ! [A_96,B_97,C_98] :
      ( k9_subset_1(A_96,B_97,C_98) = k3_xboole_0(B_97,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_379,plain,(
    ! [A_22,B_97] : k9_subset_1(A_22,B_97,'#skF_6') = k3_xboole_0(B_97,'#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_377])).

tff(c_381,plain,(
    ! [A_22,B_97] : k9_subset_1(A_22,B_97,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_379])).

tff(c_971,plain,(
    ! [A_152,B_153,D_154] :
      ( k9_subset_1(u1_struct_0(A_152),B_153,D_154) != '#skF_4'(A_152,B_153)
      | ~ v4_pre_topc(D_154,A_152)
      | ~ m1_subset_1(D_154,k1_zfmisc_1(u1_struct_0(A_152)))
      | v2_tex_2(B_153,A_152)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_974,plain,(
    ! [A_152,B_97] :
      ( '#skF_4'(A_152,B_97) != '#skF_6'
      | ~ v4_pre_topc('#skF_6',A_152)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_152)))
      | v2_tex_2(B_97,A_152)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_971])).

tff(c_1927,plain,(
    ! [A_199,B_200] :
      ( '#skF_4'(A_199,B_200) != '#skF_6'
      | ~ v4_pre_topc('#skF_6',A_199)
      | v2_tex_2(B_200,A_199)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_974])).

tff(c_1941,plain,(
    ! [A_201] :
      ( '#skF_4'(A_201,'#skF_6') != '#skF_6'
      | ~ v4_pre_topc('#skF_6',A_201)
      | v2_tex_2('#skF_6',A_201)
      | ~ l1_pre_topc(A_201) ) ),
    inference(resolution,[status(thm)],[c_82,c_1927])).

tff(c_1944,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1358,c_1941])).

tff(c_1950,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_577,c_1944])).

tff(c_1952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1950])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:15:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.63  
% 3.84/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.64  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.84/1.64  
% 3.84/1.64  %Foreground sorts:
% 3.84/1.64  
% 3.84/1.64  
% 3.84/1.64  %Background operators:
% 3.84/1.64  
% 3.84/1.64  
% 3.84/1.64  %Foreground operators:
% 3.84/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.84/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.84/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.84/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.84/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.84/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.84/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.84/1.64  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.84/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.84/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.84/1.64  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.84/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.84/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.84/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.84/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.84/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.84/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.84/1.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.84/1.64  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.84/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.84/1.64  
% 3.97/1.65  tff(f_116, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 3.97/1.65  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.97/1.65  tff(f_63, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.97/1.65  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 3.97/1.65  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.97/1.65  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.97/1.65  tff(f_51, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.97/1.65  tff(f_80, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.97/1.65  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.97/1.65  tff(f_57, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.97/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.97/1.65  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.97/1.65  tff(c_50, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.97/1.65  tff(c_56, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.97/1.65  tff(c_54, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.97/1.65  tff(c_71, plain, (![A_58]: (k1_xboole_0=A_58 | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.97/1.65  tff(c_80, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_54, c_71])).
% 3.97/1.65  tff(c_32, plain, (![A_22]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.97/1.65  tff(c_82, plain, (![A_22]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_32])).
% 3.97/1.65  tff(c_533, plain, (![A_114, B_115]: (r1_tarski('#skF_4'(A_114, B_115), B_115) | v2_tex_2(B_115, A_114) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.97/1.65  tff(c_547, plain, (![A_116]: (r1_tarski('#skF_4'(A_116, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_116) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_82, c_533])).
% 3.97/1.65  tff(c_251, plain, (![A_72, B_73]: (r2_hidden('#skF_2'(A_72, B_73), A_72) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.97/1.65  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.97/1.65  tff(c_255, plain, (![A_72, B_73]: (~v1_xboole_0(A_72) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_251, c_4])).
% 3.97/1.65  tff(c_259, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.97/1.65  tff(c_264, plain, (![B_73, A_72]: (B_73=A_72 | ~r1_tarski(B_73, A_72) | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_255, c_259])).
% 3.97/1.65  tff(c_553, plain, (![A_116]: ('#skF_4'(A_116, '#skF_6')='#skF_6' | ~v1_xboole_0('#skF_6') | v2_tex_2('#skF_6', A_116) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_547, c_264])).
% 3.97/1.65  tff(c_571, plain, (![A_118]: ('#skF_4'(A_118, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_118) | ~l1_pre_topc(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_553])).
% 3.97/1.65  tff(c_574, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_571, c_50])).
% 3.97/1.65  tff(c_577, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_574])).
% 3.97/1.65  tff(c_58, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.97/1.65  tff(c_594, plain, (![A_119, B_120]: (m1_subset_1('#skF_4'(A_119, B_120), k1_zfmisc_1(u1_struct_0(A_119))) | v2_tex_2(B_120, A_119) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.97/1.65  tff(c_36, plain, (![B_28, A_26]: (v4_pre_topc(B_28, A_26) | ~v1_xboole_0(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.97/1.65  tff(c_1336, plain, (![A_178, B_179]: (v4_pre_topc('#skF_4'(A_178, B_179), A_178) | ~v1_xboole_0('#skF_4'(A_178, B_179)) | ~v2_pre_topc(A_178) | v2_tex_2(B_179, A_178) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(resolution, [status(thm)], [c_594, c_36])).
% 3.97/1.65  tff(c_1352, plain, (![A_180]: (v4_pre_topc('#skF_4'(A_180, '#skF_6'), A_180) | ~v1_xboole_0('#skF_4'(A_180, '#skF_6')) | ~v2_pre_topc(A_180) | v2_tex_2('#skF_6', A_180) | ~l1_pre_topc(A_180))), inference(resolution, [status(thm)], [c_82, c_1336])).
% 3.97/1.65  tff(c_1355, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~v1_xboole_0('#skF_4'('#skF_5', '#skF_6')) | ~v2_pre_topc('#skF_5') | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_577, c_1352])).
% 3.97/1.65  tff(c_1357, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_54, c_577, c_1355])).
% 3.97/1.65  tff(c_1358, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_50, c_1357])).
% 3.97/1.65  tff(c_164, plain, (![A_68, B_69]: (k4_xboole_0(A_68, k4_xboole_0(A_68, B_69))=k3_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.97/1.65  tff(c_28, plain, (![A_18]: (k4_xboole_0(k1_xboole_0, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.97/1.65  tff(c_83, plain, (![A_18]: (k4_xboole_0('#skF_6', A_18)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_28])).
% 3.97/1.65  tff(c_194, plain, (![B_70]: (k3_xboole_0('#skF_6', B_70)='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_164, c_83])).
% 3.97/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.97/1.65  tff(c_199, plain, (![B_70]: (k3_xboole_0(B_70, '#skF_6')='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_194, c_2])).
% 3.97/1.65  tff(c_377, plain, (![A_96, B_97, C_98]: (k9_subset_1(A_96, B_97, C_98)=k3_xboole_0(B_97, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.97/1.65  tff(c_379, plain, (![A_22, B_97]: (k9_subset_1(A_22, B_97, '#skF_6')=k3_xboole_0(B_97, '#skF_6'))), inference(resolution, [status(thm)], [c_82, c_377])).
% 3.97/1.65  tff(c_381, plain, (![A_22, B_97]: (k9_subset_1(A_22, B_97, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_379])).
% 3.97/1.65  tff(c_971, plain, (![A_152, B_153, D_154]: (k9_subset_1(u1_struct_0(A_152), B_153, D_154)!='#skF_4'(A_152, B_153) | ~v4_pre_topc(D_154, A_152) | ~m1_subset_1(D_154, k1_zfmisc_1(u1_struct_0(A_152))) | v2_tex_2(B_153, A_152) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.97/1.65  tff(c_974, plain, (![A_152, B_97]: ('#skF_4'(A_152, B_97)!='#skF_6' | ~v4_pre_topc('#skF_6', A_152) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_152))) | v2_tex_2(B_97, A_152) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(superposition, [status(thm), theory('equality')], [c_381, c_971])).
% 3.97/1.65  tff(c_1927, plain, (![A_199, B_200]: ('#skF_4'(A_199, B_200)!='#skF_6' | ~v4_pre_topc('#skF_6', A_199) | v2_tex_2(B_200, A_199) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_974])).
% 3.97/1.65  tff(c_1941, plain, (![A_201]: ('#skF_4'(A_201, '#skF_6')!='#skF_6' | ~v4_pre_topc('#skF_6', A_201) | v2_tex_2('#skF_6', A_201) | ~l1_pre_topc(A_201))), inference(resolution, [status(thm)], [c_82, c_1927])).
% 3.97/1.65  tff(c_1944, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1358, c_1941])).
% 3.97/1.65  tff(c_1950, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_577, c_1944])).
% 3.97/1.65  tff(c_1952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1950])).
% 3.97/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.65  
% 3.97/1.65  Inference rules
% 3.97/1.65  ----------------------
% 3.97/1.65  #Ref     : 0
% 3.97/1.65  #Sup     : 437
% 3.97/1.65  #Fact    : 2
% 3.97/1.65  #Define  : 0
% 3.97/1.65  #Split   : 1
% 3.97/1.65  #Chain   : 0
% 3.97/1.65  #Close   : 0
% 3.97/1.65  
% 3.97/1.65  Ordering : KBO
% 3.97/1.65  
% 3.97/1.65  Simplification rules
% 3.97/1.65  ----------------------
% 3.97/1.65  #Subsume      : 76
% 3.97/1.65  #Demod        : 420
% 3.97/1.65  #Tautology    : 226
% 3.97/1.65  #SimpNegUnit  : 20
% 3.97/1.65  #BackRed      : 11
% 3.97/1.65  
% 3.97/1.65  #Partial instantiations: 0
% 3.97/1.65  #Strategies tried      : 1
% 3.97/1.65  
% 3.97/1.65  Timing (in seconds)
% 3.97/1.65  ----------------------
% 3.97/1.65  Preprocessing        : 0.32
% 3.97/1.65  Parsing              : 0.17
% 3.97/1.65  CNF conversion       : 0.02
% 3.97/1.65  Main loop            : 0.58
% 3.97/1.66  Inferencing          : 0.18
% 3.97/1.66  Reduction            : 0.23
% 3.97/1.66  Demodulation         : 0.19
% 3.97/1.66  BG Simplification    : 0.03
% 3.97/1.66  Subsumption          : 0.10
% 3.97/1.66  Abstraction          : 0.03
% 3.97/1.66  MUC search           : 0.00
% 3.97/1.66  Cooper               : 0.00
% 3.97/1.66  Total                : 0.93
% 3.97/1.66  Index Insertion      : 0.00
% 3.97/1.66  Index Deletion       : 0.00
% 3.97/1.66  Index Matching       : 0.00
% 3.97/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
