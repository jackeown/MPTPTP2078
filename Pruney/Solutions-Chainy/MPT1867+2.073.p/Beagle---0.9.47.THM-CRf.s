%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:32 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 4.67s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 158 expanded)
%              Number of leaves         :   41 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  131 ( 315 expanded)
%              Number of equality atoms :   30 (  58 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_65,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_106,axiom,(
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

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(c_62,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_60,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    ! [A_28] :
      ( v3_pre_topc(k2_struct_0(A_28),A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [A_17] : k2_subset_1(A_17) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    ! [A_18] : m1_subset_1(k2_subset_1(A_18),k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_65,plain,(
    ! [A_18] : m1_subset_1(A_18,k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_54,plain,(
    ~ v2_tex_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_58,plain,(
    v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_77,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_58,c_77])).

tff(c_32,plain,(
    ! [A_22] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_95,plain,(
    ! [A_22] : m1_subset_1('#skF_6',k1_zfmisc_1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_32])).

tff(c_38,plain,(
    ! [A_27] :
      ( l1_struct_0(A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_119,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_125,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_38,c_119])).

tff(c_129,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_125])).

tff(c_389,plain,(
    ! [A_115,B_116] :
      ( r1_tarski('#skF_4'(A_115,B_116),B_116)
      | v2_tex_2(B_116,A_115)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_400,plain,(
    ! [B_116] :
      ( r1_tarski('#skF_4'('#skF_5',B_116),B_116)
      | v2_tex_2(B_116,'#skF_5')
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_389])).

tff(c_464,plain,(
    ! [B_122] :
      ( r1_tarski('#skF_4'('#skF_5',B_122),B_122)
      | v2_tex_2(B_122,'#skF_5')
      | ~ m1_subset_1(B_122,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_400])).

tff(c_485,plain,
    ( r1_tarski('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v2_tex_2('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_95,c_464])).

tff(c_494,plain,(
    r1_tarski('#skF_4'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_485])).

tff(c_135,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_2'(A_71,B_72),A_71)
      | r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_145,plain,(
    ! [A_71,B_72] :
      ( ~ v1_xboole_0(A_71)
      | r1_tarski(A_71,B_72) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_147,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(B_75,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_152,plain,(
    ! [B_72,A_71] :
      ( B_72 = A_71
      | ~ r1_tarski(B_72,A_71)
      | ~ v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_145,c_147])).

tff(c_500,plain,
    ( '#skF_4'('#skF_5','#skF_6') = '#skF_6'
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_494,c_152])).

tff(c_508,plain,(
    '#skF_4'('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_500])).

tff(c_22,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_99,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_22])).

tff(c_219,plain,(
    ! [A_96,B_97,C_98] :
      ( k9_subset_1(A_96,B_97,C_98) = k3_xboole_0(B_97,C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_232,plain,(
    ! [A_22,B_97] : k9_subset_1(A_22,B_97,'#skF_6') = k3_xboole_0(B_97,'#skF_6') ),
    inference(resolution,[status(thm)],[c_95,c_219])).

tff(c_238,plain,(
    ! [A_22,B_97] : k9_subset_1(A_22,B_97,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_232])).

tff(c_281,plain,(
    ! [A_105,C_106,B_107] :
      ( k9_subset_1(A_105,C_106,B_107) = k9_subset_1(A_105,B_107,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_294,plain,(
    ! [A_22,B_107] : k9_subset_1(A_22,B_107,'#skF_6') = k9_subset_1(A_22,'#skF_6',B_107) ),
    inference(resolution,[status(thm)],[c_95,c_281])).

tff(c_301,plain,(
    ! [A_22,B_107] : k9_subset_1(A_22,'#skF_6',B_107) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_294])).

tff(c_987,plain,(
    ! [A_166,B_167,D_168] :
      ( k9_subset_1(u1_struct_0(A_166),B_167,D_168) != '#skF_4'(A_166,B_167)
      | ~ v3_pre_topc(D_168,A_166)
      | ~ m1_subset_1(D_168,k1_zfmisc_1(u1_struct_0(A_166)))
      | v2_tex_2(B_167,A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1001,plain,(
    ! [B_167,D_168] :
      ( k9_subset_1(k2_struct_0('#skF_5'),B_167,D_168) != '#skF_4'('#skF_5',B_167)
      | ~ v3_pre_topc(D_168,'#skF_5')
      | ~ m1_subset_1(D_168,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_tex_2(B_167,'#skF_5')
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_987])).

tff(c_2477,plain,(
    ! [B_272,D_273] :
      ( k9_subset_1(k2_struct_0('#skF_5'),B_272,D_273) != '#skF_4'('#skF_5',B_272)
      | ~ v3_pre_topc(D_273,'#skF_5')
      | ~ m1_subset_1(D_273,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_tex_2(B_272,'#skF_5')
      | ~ m1_subset_1(B_272,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_129,c_129,c_1001])).

tff(c_2495,plain,(
    ! [B_107] :
      ( '#skF_4'('#skF_5','#skF_6') != '#skF_6'
      | ~ v3_pre_topc(B_107,'#skF_5')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_tex_2('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_2477])).

tff(c_2505,plain,(
    ! [B_107] :
      ( ~ v3_pre_topc(B_107,'#skF_5')
      | ~ m1_subset_1(B_107,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_tex_2('#skF_6','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_508,c_2495])).

tff(c_2511,plain,(
    ! [B_274] :
      ( ~ v3_pre_topc(B_274,'#skF_5')
      | ~ m1_subset_1(B_274,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2505])).

tff(c_2573,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_65,c_2511])).

tff(c_2577,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_2573])).

tff(c_2581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2577])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.83  
% 4.67/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.83  %$ v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.67/1.83  
% 4.67/1.83  %Foreground sorts:
% 4.67/1.83  
% 4.67/1.83  
% 4.67/1.83  %Background operators:
% 4.67/1.83  
% 4.67/1.83  
% 4.67/1.83  %Foreground operators:
% 4.67/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.67/1.83  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.67/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.67/1.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.67/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.67/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.67/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.67/1.83  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.67/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.67/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.67/1.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.67/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.67/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.67/1.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.67/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.67/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.67/1.83  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.67/1.83  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.67/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.67/1.83  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.67/1.83  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.67/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.67/1.83  
% 4.67/1.85  tff(f_121, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 4.67/1.85  tff(f_85, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.67/1.85  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.67/1.85  tff(f_59, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.67/1.85  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.67/1.85  tff(f_65, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.67/1.85  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.67/1.85  tff(f_75, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.67/1.85  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tex_2)).
% 4.67/1.85  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.67/1.85  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.67/1.85  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.67/1.85  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.67/1.85  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.67/1.85  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.67/1.85  tff(c_62, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.67/1.85  tff(c_60, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.67/1.85  tff(c_40, plain, (![A_28]: (v3_pre_topc(k2_struct_0(A_28), A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.67/1.85  tff(c_26, plain, (![A_17]: (k2_subset_1(A_17)=A_17)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.67/1.85  tff(c_28, plain, (![A_18]: (m1_subset_1(k2_subset_1(A_18), k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.67/1.85  tff(c_65, plain, (![A_18]: (m1_subset_1(A_18, k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 4.67/1.85  tff(c_54, plain, (~v2_tex_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.67/1.85  tff(c_58, plain, (v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.67/1.85  tff(c_77, plain, (![A_57]: (k1_xboole_0=A_57 | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.67/1.85  tff(c_86, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_58, c_77])).
% 4.67/1.85  tff(c_32, plain, (![A_22]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.67/1.85  tff(c_95, plain, (![A_22]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_32])).
% 4.67/1.85  tff(c_38, plain, (![A_27]: (l1_struct_0(A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.67/1.85  tff(c_119, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.67/1.85  tff(c_125, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_38, c_119])).
% 4.67/1.85  tff(c_129, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_125])).
% 4.67/1.85  tff(c_389, plain, (![A_115, B_116]: (r1_tarski('#skF_4'(A_115, B_116), B_116) | v2_tex_2(B_116, A_115) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.67/1.85  tff(c_400, plain, (![B_116]: (r1_tarski('#skF_4'('#skF_5', B_116), B_116) | v2_tex_2(B_116, '#skF_5') | ~m1_subset_1(B_116, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_389])).
% 4.67/1.85  tff(c_464, plain, (![B_122]: (r1_tarski('#skF_4'('#skF_5', B_122), B_122) | v2_tex_2(B_122, '#skF_5') | ~m1_subset_1(B_122, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_400])).
% 4.67/1.85  tff(c_485, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v2_tex_2('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_95, c_464])).
% 4.67/1.85  tff(c_494, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_54, c_485])).
% 4.67/1.85  tff(c_135, plain, (![A_71, B_72]: (r2_hidden('#skF_2'(A_71, B_72), A_71) | r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.67/1.85  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.67/1.85  tff(c_145, plain, (![A_71, B_72]: (~v1_xboole_0(A_71) | r1_tarski(A_71, B_72))), inference(resolution, [status(thm)], [c_135, c_2])).
% 4.67/1.85  tff(c_147, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(B_75, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.67/1.85  tff(c_152, plain, (![B_72, A_71]: (B_72=A_71 | ~r1_tarski(B_72, A_71) | ~v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_145, c_147])).
% 4.67/1.85  tff(c_500, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6' | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_494, c_152])).
% 4.67/1.85  tff(c_508, plain, ('#skF_4'('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_500])).
% 4.67/1.85  tff(c_22, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.67/1.85  tff(c_99, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_86, c_22])).
% 4.67/1.85  tff(c_219, plain, (![A_96, B_97, C_98]: (k9_subset_1(A_96, B_97, C_98)=k3_xboole_0(B_97, C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.67/1.85  tff(c_232, plain, (![A_22, B_97]: (k9_subset_1(A_22, B_97, '#skF_6')=k3_xboole_0(B_97, '#skF_6'))), inference(resolution, [status(thm)], [c_95, c_219])).
% 4.67/1.85  tff(c_238, plain, (![A_22, B_97]: (k9_subset_1(A_22, B_97, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_232])).
% 4.67/1.85  tff(c_281, plain, (![A_105, C_106, B_107]: (k9_subset_1(A_105, C_106, B_107)=k9_subset_1(A_105, B_107, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.67/1.85  tff(c_294, plain, (![A_22, B_107]: (k9_subset_1(A_22, B_107, '#skF_6')=k9_subset_1(A_22, '#skF_6', B_107))), inference(resolution, [status(thm)], [c_95, c_281])).
% 4.67/1.85  tff(c_301, plain, (![A_22, B_107]: (k9_subset_1(A_22, '#skF_6', B_107)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_294])).
% 4.67/1.85  tff(c_987, plain, (![A_166, B_167, D_168]: (k9_subset_1(u1_struct_0(A_166), B_167, D_168)!='#skF_4'(A_166, B_167) | ~v3_pre_topc(D_168, A_166) | ~m1_subset_1(D_168, k1_zfmisc_1(u1_struct_0(A_166))) | v2_tex_2(B_167, A_166) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.67/1.85  tff(c_1001, plain, (![B_167, D_168]: (k9_subset_1(k2_struct_0('#skF_5'), B_167, D_168)!='#skF_4'('#skF_5', B_167) | ~v3_pre_topc(D_168, '#skF_5') | ~m1_subset_1(D_168, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_tex_2(B_167, '#skF_5') | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_987])).
% 4.67/1.85  tff(c_2477, plain, (![B_272, D_273]: (k9_subset_1(k2_struct_0('#skF_5'), B_272, D_273)!='#skF_4'('#skF_5', B_272) | ~v3_pre_topc(D_273, '#skF_5') | ~m1_subset_1(D_273, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_tex_2(B_272, '#skF_5') | ~m1_subset_1(B_272, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_129, c_129, c_1001])).
% 4.67/1.85  tff(c_2495, plain, (![B_107]: ('#skF_4'('#skF_5', '#skF_6')!='#skF_6' | ~v3_pre_topc(B_107, '#skF_5') | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_tex_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_301, c_2477])).
% 4.67/1.85  tff(c_2505, plain, (![B_107]: (~v3_pre_topc(B_107, '#skF_5') | ~m1_subset_1(B_107, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_tex_2('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_508, c_2495])).
% 4.67/1.85  tff(c_2511, plain, (![B_274]: (~v3_pre_topc(B_274, '#skF_5') | ~m1_subset_1(B_274, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_2505])).
% 4.67/1.85  tff(c_2573, plain, (~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_65, c_2511])).
% 4.67/1.85  tff(c_2577, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_2573])).
% 4.67/1.85  tff(c_2581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2577])).
% 4.67/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.67/1.85  
% 4.67/1.85  Inference rules
% 4.67/1.85  ----------------------
% 4.67/1.85  #Ref     : 0
% 4.67/1.85  #Sup     : 567
% 4.67/1.85  #Fact    : 2
% 4.67/1.85  #Define  : 0
% 4.67/1.85  #Split   : 3
% 4.67/1.85  #Chain   : 0
% 4.67/1.85  #Close   : 0
% 4.67/1.85  
% 4.67/1.85  Ordering : KBO
% 4.67/1.85  
% 4.67/1.85  Simplification rules
% 4.67/1.85  ----------------------
% 4.67/1.85  #Subsume      : 106
% 4.67/1.85  #Demod        : 206
% 4.67/1.85  #Tautology    : 129
% 4.67/1.85  #SimpNegUnit  : 27
% 4.67/1.85  #BackRed      : 14
% 4.67/1.85  
% 4.67/1.85  #Partial instantiations: 0
% 4.67/1.85  #Strategies tried      : 1
% 4.67/1.85  
% 4.67/1.85  Timing (in seconds)
% 4.67/1.85  ----------------------
% 4.67/1.85  Preprocessing        : 0.34
% 4.67/1.85  Parsing              : 0.19
% 4.67/1.85  CNF conversion       : 0.02
% 4.67/1.85  Main loop            : 0.72
% 4.67/1.85  Inferencing          : 0.24
% 4.67/1.85  Reduction            : 0.22
% 4.67/1.85  Demodulation         : 0.16
% 4.67/1.85  BG Simplification    : 0.04
% 4.67/1.85  Subsumption          : 0.16
% 4.67/1.85  Abstraction          : 0.05
% 4.67/1.85  MUC search           : 0.00
% 4.67/1.85  Cooper               : 0.00
% 4.67/1.85  Total                : 1.09
% 4.67/1.85  Index Insertion      : 0.00
% 4.67/1.85  Index Deletion       : 0.00
% 4.67/1.85  Index Matching       : 0.00
% 4.67/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
