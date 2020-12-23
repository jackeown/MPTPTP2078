%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:33 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 149 expanded)
%              Number of leaves         :   35 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 314 expanded)
%              Number of equality atoms :   26 (  51 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_99,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_46,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_52,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_59,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_50,c_59])).

tff(c_26,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_84,plain,(
    ! [A_17] : m1_subset_1('#skF_6',k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_26])).

tff(c_273,plain,(
    ! [A_101,B_102] :
      ( r1_tarski('#skF_4'(A_101,B_102),B_102)
      | v2_tex_2(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_303,plain,(
    ! [A_105] :
      ( r1_tarski('#skF_4'(A_105,'#skF_6'),'#skF_6')
      | v2_tex_2('#skF_6',A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_84,c_273])).

tff(c_107,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_66,B_67] :
      ( ~ v1_xboole_0(A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,(
    ! [B_67,A_66] :
      ( B_67 = A_66
      | ~ r1_tarski(B_67,A_66)
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_118,c_16])).

tff(c_309,plain,(
    ! [A_105] :
      ( '#skF_4'(A_105,'#skF_6') = '#skF_6'
      | ~ v1_xboole_0('#skF_6')
      | v2_tex_2('#skF_6',A_105)
      | ~ l1_pre_topc(A_105) ) ),
    inference(resolution,[status(thm)],[c_303,c_121])).

tff(c_330,plain,(
    ! [A_107] :
      ( '#skF_4'(A_107,'#skF_6') = '#skF_6'
      | v2_tex_2('#skF_6',A_107)
      | ~ l1_pre_topc(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_309])).

tff(c_333,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_330,c_46])).

tff(c_336,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_333])).

tff(c_54,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_199,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k1_tops_1(A_91,B_92),B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_208,plain,(
    ! [A_93] :
      ( r1_tarski(k1_tops_1(A_93,'#skF_6'),'#skF_6')
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_84,c_199])).

tff(c_214,plain,(
    ! [A_93] :
      ( k1_tops_1(A_93,'#skF_6') = '#skF_6'
      | ~ v1_xboole_0('#skF_6')
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_208,c_121])).

tff(c_232,plain,(
    ! [A_95] :
      ( k1_tops_1(A_95,'#skF_6') = '#skF_6'
      | ~ l1_pre_topc(A_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_214])).

tff(c_236,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_52,c_232])).

tff(c_251,plain,(
    ! [A_96,B_97] :
      ( v3_pre_topc(k1_tops_1(A_96,B_97),A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_267,plain,(
    ! [A_100] :
      ( v3_pre_topc(k1_tops_1(A_100,'#skF_6'),A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_84,c_251])).

tff(c_270,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_267])).

tff(c_272,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_270])).

tff(c_22,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_22])).

tff(c_164,plain,(
    ! [A_82,B_83,C_84] :
      ( k9_subset_1(A_82,B_83,C_84) = k3_xboole_0(B_83,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_166,plain,(
    ! [A_17,B_83] : k9_subset_1(A_17,B_83,'#skF_6') = k3_xboole_0(B_83,'#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_164])).

tff(c_168,plain,(
    ! [A_17,B_83] : k9_subset_1(A_17,B_83,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_166])).

tff(c_521,plain,(
    ! [A_127,B_128,D_129] :
      ( k9_subset_1(u1_struct_0(A_127),B_128,D_129) != '#skF_4'(A_127,B_128)
      | ~ v3_pre_topc(D_129,A_127)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(u1_struct_0(A_127)))
      | v2_tex_2(B_128,A_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_524,plain,(
    ! [A_127,B_83] :
      ( '#skF_4'(A_127,B_83) != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_127)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_127)))
      | v2_tex_2(B_83,A_127)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_521])).

tff(c_1129,plain,(
    ! [A_183,B_184] :
      ( '#skF_4'(A_183,B_184) != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_183)
      | v2_tex_2(B_184,A_183)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_524])).

tff(c_1143,plain,(
    ! [A_185] :
      ( '#skF_4'(A_185,'#skF_6') != '#skF_6'
      | ~ v3_pre_topc('#skF_6',A_185)
      | v2_tex_2('#skF_6',A_185)
      | ~ l1_pre_topc(A_185) ) ),
    inference(resolution,[status(thm)],[c_84,c_1129])).

tff(c_1146,plain,
    ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
    | v2_tex_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_272,c_1143])).

tff(c_1149,plain,(
    v2_tex_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_336,c_1146])).

tff(c_1151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.54  
% 3.10/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.54  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.32/1.54  
% 3.32/1.54  %Foreground sorts:
% 3.32/1.54  
% 3.32/1.54  
% 3.32/1.54  %Background operators:
% 3.32/1.54  
% 3.32/1.54  
% 3.32/1.54  %Foreground operators:
% 3.32/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.32/1.54  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.32/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.32/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.32/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.54  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.32/1.54  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.32/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.32/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.32/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.32/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.32/1.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.32/1.54  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.32/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.54  
% 3.34/1.55  tff(f_114, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.34/1.55  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.34/1.55  tff(f_57, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.34/1.55  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 3.34/1.55  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.34/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.34/1.55  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.34/1.55  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.34/1.55  tff(f_71, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.34/1.55  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.34/1.55  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.34/1.55  tff(c_46, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.34/1.55  tff(c_52, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.34/1.55  tff(c_50, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.34/1.55  tff(c_59, plain, (![A_53]: (k1_xboole_0=A_53 | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.55  tff(c_68, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_50, c_59])).
% 3.34/1.55  tff(c_26, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.34/1.55  tff(c_84, plain, (![A_17]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_26])).
% 3.34/1.55  tff(c_273, plain, (![A_101, B_102]: (r1_tarski('#skF_4'(A_101, B_102), B_102) | v2_tex_2(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.34/1.55  tff(c_303, plain, (![A_105]: (r1_tarski('#skF_4'(A_105, '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', A_105) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_84, c_273])).
% 3.34/1.55  tff(c_107, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.34/1.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.55  tff(c_118, plain, (![A_66, B_67]: (~v1_xboole_0(A_66) | r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_107, c_2])).
% 3.34/1.55  tff(c_16, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.34/1.55  tff(c_121, plain, (![B_67, A_66]: (B_67=A_66 | ~r1_tarski(B_67, A_66) | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_118, c_16])).
% 3.34/1.55  tff(c_309, plain, (![A_105]: ('#skF_4'(A_105, '#skF_6')='#skF_6' | ~v1_xboole_0('#skF_6') | v2_tex_2('#skF_6', A_105) | ~l1_pre_topc(A_105))), inference(resolution, [status(thm)], [c_303, c_121])).
% 3.34/1.55  tff(c_330, plain, (![A_107]: ('#skF_4'(A_107, '#skF_6')='#skF_6' | v2_tex_2('#skF_6', A_107) | ~l1_pre_topc(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_309])).
% 3.34/1.55  tff(c_333, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_330, c_46])).
% 3.34/1.55  tff(c_336, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_333])).
% 3.34/1.55  tff(c_54, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.34/1.55  tff(c_199, plain, (![A_91, B_92]: (r1_tarski(k1_tops_1(A_91, B_92), B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.34/1.55  tff(c_208, plain, (![A_93]: (r1_tarski(k1_tops_1(A_93, '#skF_6'), '#skF_6') | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_84, c_199])).
% 3.34/1.55  tff(c_214, plain, (![A_93]: (k1_tops_1(A_93, '#skF_6')='#skF_6' | ~v1_xboole_0('#skF_6') | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_208, c_121])).
% 3.34/1.55  tff(c_232, plain, (![A_95]: (k1_tops_1(A_95, '#skF_6')='#skF_6' | ~l1_pre_topc(A_95))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_214])).
% 3.34/1.55  tff(c_236, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_52, c_232])).
% 3.34/1.55  tff(c_251, plain, (![A_96, B_97]: (v3_pre_topc(k1_tops_1(A_96, B_97), A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_96))) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.34/1.55  tff(c_267, plain, (![A_100]: (v3_pre_topc(k1_tops_1(A_100, '#skF_6'), A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100))), inference(resolution, [status(thm)], [c_84, c_251])).
% 3.34/1.55  tff(c_270, plain, (v3_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_236, c_267])).
% 3.34/1.55  tff(c_272, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_270])).
% 3.34/1.55  tff(c_22, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.34/1.55  tff(c_76, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_22])).
% 3.34/1.55  tff(c_164, plain, (![A_82, B_83, C_84]: (k9_subset_1(A_82, B_83, C_84)=k3_xboole_0(B_83, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.34/1.55  tff(c_166, plain, (![A_17, B_83]: (k9_subset_1(A_17, B_83, '#skF_6')=k3_xboole_0(B_83, '#skF_6'))), inference(resolution, [status(thm)], [c_84, c_164])).
% 3.34/1.55  tff(c_168, plain, (![A_17, B_83]: (k9_subset_1(A_17, B_83, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_166])).
% 3.34/1.55  tff(c_521, plain, (![A_127, B_128, D_129]: (k9_subset_1(u1_struct_0(A_127), B_128, D_129)!='#skF_4'(A_127, B_128) | ~v3_pre_topc(D_129, A_127) | ~m1_subset_1(D_129, k1_zfmisc_1(u1_struct_0(A_127))) | v2_tex_2(B_128, A_127) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.34/1.55  tff(c_524, plain, (![A_127, B_83]: ('#skF_4'(A_127, B_83)!='#skF_6' | ~v3_pre_topc('#skF_6', A_127) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_127))) | v2_tex_2(B_83, A_127) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(superposition, [status(thm), theory('equality')], [c_168, c_521])).
% 3.34/1.55  tff(c_1129, plain, (![A_183, B_184]: ('#skF_4'(A_183, B_184)!='#skF_6' | ~v3_pre_topc('#skF_6', A_183) | v2_tex_2(B_184, A_183) | ~m1_subset_1(B_184, k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_524])).
% 3.34/1.55  tff(c_1143, plain, (![A_185]: ('#skF_4'(A_185, '#skF_6')!='#skF_6' | ~v3_pre_topc('#skF_6', A_185) | v2_tex_2('#skF_6', A_185) | ~l1_pre_topc(A_185))), inference(resolution, [status(thm)], [c_84, c_1129])).
% 3.34/1.55  tff(c_1146, plain, ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | v2_tex_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_272, c_1143])).
% 3.34/1.55  tff(c_1149, plain, (v2_tex_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_336, c_1146])).
% 3.34/1.55  tff(c_1151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1149])).
% 3.34/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.55  
% 3.34/1.55  Inference rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Ref     : 0
% 3.34/1.55  #Sup     : 241
% 3.34/1.55  #Fact    : 2
% 3.34/1.55  #Define  : 0
% 3.34/1.55  #Split   : 1
% 3.34/1.55  #Chain   : 0
% 3.34/1.55  #Close   : 0
% 3.34/1.55  
% 3.34/1.55  Ordering : KBO
% 3.34/1.55  
% 3.34/1.55  Simplification rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Subsume      : 97
% 3.34/1.55  #Demod        : 106
% 3.34/1.55  #Tautology    : 60
% 3.34/1.55  #SimpNegUnit  : 22
% 3.34/1.55  #BackRed      : 10
% 3.34/1.55  
% 3.34/1.55  #Partial instantiations: 0
% 3.34/1.55  #Strategies tried      : 1
% 3.34/1.55  
% 3.34/1.55  Timing (in seconds)
% 3.34/1.55  ----------------------
% 3.34/1.56  Preprocessing        : 0.30
% 3.34/1.56  Parsing              : 0.15
% 3.34/1.56  CNF conversion       : 0.02
% 3.34/1.56  Main loop            : 0.41
% 3.34/1.56  Inferencing          : 0.14
% 3.34/1.56  Reduction            : 0.12
% 3.34/1.56  Demodulation         : 0.07
% 3.34/1.56  BG Simplification    : 0.02
% 3.34/1.56  Subsumption          : 0.10
% 3.34/1.56  Abstraction          : 0.02
% 3.34/1.56  MUC search           : 0.00
% 3.34/1.56  Cooper               : 0.00
% 3.34/1.56  Total                : 0.74
% 3.34/1.56  Index Insertion      : 0.00
% 3.34/1.56  Index Deletion       : 0.00
% 3.34/1.56  Index Matching       : 0.00
% 3.34/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
