%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:29 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 207 expanded)
%              Number of leaves         :   32 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  126 ( 414 expanded)
%              Number of equality atoms :   23 (  74 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_98,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(c_44,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_48,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_48])).

tff(c_16,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_54,plain,(
    ! [A_17] : m1_subset_1('#skF_5',k1_zfmisc_1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_104,plain,(
    ! [A_74,B_75,C_76] :
      ( k9_subset_1(A_74,B_75,C_76) = k3_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_107,plain,(
    ! [A_17,B_75] : k9_subset_1(A_17,B_75,'#skF_5') = k3_xboole_0(B_75,'#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_104])).

tff(c_130,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1(k9_subset_1(A_79,B_80,C_81),k1_zfmisc_1(A_79))
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_139,plain,(
    ! [B_75,A_17] :
      ( m1_subset_1(k3_xboole_0(B_75,'#skF_5'),k1_zfmisc_1(A_17))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_130])).

tff(c_161,plain,(
    ! [B_84,A_85] : m1_subset_1(k3_xboole_0(B_84,'#skF_5'),k1_zfmisc_1(A_85)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_139])).

tff(c_20,plain,(
    ! [C_23,B_22,A_21] :
      ( ~ v1_xboole_0(C_23)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(C_23))
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_177,plain,(
    ! [A_85,A_21,B_84] :
      ( ~ v1_xboole_0(A_85)
      | ~ r2_hidden(A_21,k3_xboole_0(B_84,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_161,c_20])).

tff(c_194,plain,(
    ! [A_89,B_90] : ~ r2_hidden(A_89,k3_xboole_0(B_90,'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_202,plain,(
    ! [B_91] : v1_xboole_0(k3_xboole_0(B_91,'#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_194])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_53,plain,(
    ! [A_5] :
      ( A_5 = '#skF_5'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6])).

tff(c_208,plain,(
    ! [B_91] : k3_xboole_0(B_91,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_202,c_53])).

tff(c_181,plain,(
    ! [A_87,B_88] :
      ( r1_tarski('#skF_3'(A_87,B_88),B_88)
      | v2_tex_2(B_88,A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_264,plain,(
    ! [A_97] :
      ( r1_tarski('#skF_3'(A_97,'#skF_5'),'#skF_5')
      | v2_tex_2('#skF_5',A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_54,c_181])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_267,plain,(
    ! [A_97] :
      ( k3_xboole_0('#skF_3'(A_97,'#skF_5'),'#skF_5') = '#skF_3'(A_97,'#skF_5')
      | v2_tex_2('#skF_5',A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(resolution,[status(thm)],[c_264,c_8])).

tff(c_270,plain,(
    ! [A_98] :
      ( '#skF_3'(A_98,'#skF_5') = '#skF_5'
      | v2_tex_2('#skF_5',A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_267])).

tff(c_36,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_273,plain,
    ( '#skF_3'('#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_270,c_36])).

tff(c_276,plain,(
    '#skF_3'('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_273])).

tff(c_148,plain,(
    ! [B_82,A_83] :
      ( v4_pre_topc(B_82,A_83)
      | ~ v1_xboole_0(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_156,plain,(
    ! [A_83] :
      ( v4_pre_topc('#skF_5',A_83)
      | ~ v1_xboole_0('#skF_5')
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_54,c_148])).

tff(c_160,plain,(
    ! [A_83] :
      ( v4_pre_topc('#skF_5',A_83)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_156])).

tff(c_214,plain,(
    ! [A_17,B_75] : k9_subset_1(A_17,B_75,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_107])).

tff(c_533,plain,(
    ! [A_140,B_141,D_142] :
      ( k9_subset_1(u1_struct_0(A_140),B_141,D_142) != '#skF_3'(A_140,B_141)
      | ~ v4_pre_topc(D_142,A_140)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(u1_struct_0(A_140)))
      | v2_tex_2(B_141,A_140)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_536,plain,(
    ! [A_140,B_75] :
      ( '#skF_3'(A_140,B_75) != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_140)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_140)))
      | v2_tex_2(B_75,A_140)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_533])).

tff(c_757,plain,(
    ! [A_162,B_163] :
      ( '#skF_3'(A_162,B_163) != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_162)
      | v2_tex_2(B_163,A_162)
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_536])).

tff(c_791,plain,(
    ! [A_164] :
      ( '#skF_3'(A_164,'#skF_5') != '#skF_5'
      | ~ v4_pre_topc('#skF_5',A_164)
      | v2_tex_2('#skF_5',A_164)
      | ~ l1_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_54,c_757])).

tff(c_806,plain,(
    ! [A_168] :
      ( '#skF_3'(A_168,'#skF_5') != '#skF_5'
      | v2_tex_2('#skF_5',A_168)
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168) ) ),
    inference(resolution,[status(thm)],[c_160,c_791])).

tff(c_809,plain,
    ( '#skF_3'('#skF_4','#skF_5') != '#skF_5'
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_806,c_36])).

tff(c_813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_276,c_809])).

tff(c_814,plain,(
    ! [A_85] : ~ v1_xboole_0(A_85) ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_814,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:24:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  
% 3.04/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.47  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 3.04/1.47  
% 3.04/1.47  %Foreground sorts:
% 3.04/1.47  
% 3.04/1.47  
% 3.04/1.47  %Background operators:
% 3.04/1.47  
% 3.04/1.47  
% 3.04/1.47  %Foreground operators:
% 3.04/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.04/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.04/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.04/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.04/1.47  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.04/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.04/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.04/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.04/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.04/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.04/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.04/1.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.04/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.04/1.47  
% 3.04/1.48  tff(f_113, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 3.04/1.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.04/1.48  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.04/1.48  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.04/1.48  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.04/1.48  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.04/1.48  tff(f_66, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.04/1.48  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 3.04/1.48  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.04/1.48  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.04/1.48  tff(c_44, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.04/1.48  tff(c_42, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.04/1.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.04/1.48  tff(c_40, plain, (v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.04/1.48  tff(c_48, plain, (![A_54]: (k1_xboole_0=A_54 | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.04/1.48  tff(c_52, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_40, c_48])).
% 3.04/1.48  tff(c_16, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.04/1.48  tff(c_54, plain, (![A_17]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16])).
% 3.04/1.48  tff(c_104, plain, (![A_74, B_75, C_76]: (k9_subset_1(A_74, B_75, C_76)=k3_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.04/1.48  tff(c_107, plain, (![A_17, B_75]: (k9_subset_1(A_17, B_75, '#skF_5')=k3_xboole_0(B_75, '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_104])).
% 3.04/1.48  tff(c_130, plain, (![A_79, B_80, C_81]: (m1_subset_1(k9_subset_1(A_79, B_80, C_81), k1_zfmisc_1(A_79)) | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.04/1.48  tff(c_139, plain, (![B_75, A_17]: (m1_subset_1(k3_xboole_0(B_75, '#skF_5'), k1_zfmisc_1(A_17)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_130])).
% 3.04/1.48  tff(c_161, plain, (![B_84, A_85]: (m1_subset_1(k3_xboole_0(B_84, '#skF_5'), k1_zfmisc_1(A_85)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_139])).
% 3.04/1.48  tff(c_20, plain, (![C_23, B_22, A_21]: (~v1_xboole_0(C_23) | ~m1_subset_1(B_22, k1_zfmisc_1(C_23)) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.04/1.48  tff(c_177, plain, (![A_85, A_21, B_84]: (~v1_xboole_0(A_85) | ~r2_hidden(A_21, k3_xboole_0(B_84, '#skF_5')))), inference(resolution, [status(thm)], [c_161, c_20])).
% 3.04/1.48  tff(c_194, plain, (![A_89, B_90]: (~r2_hidden(A_89, k3_xboole_0(B_90, '#skF_5')))), inference(splitLeft, [status(thm)], [c_177])).
% 3.04/1.48  tff(c_202, plain, (![B_91]: (v1_xboole_0(k3_xboole_0(B_91, '#skF_5')))), inference(resolution, [status(thm)], [c_4, c_194])).
% 3.04/1.48  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.04/1.48  tff(c_53, plain, (![A_5]: (A_5='#skF_5' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6])).
% 3.04/1.48  tff(c_208, plain, (![B_91]: (k3_xboole_0(B_91, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_202, c_53])).
% 3.04/1.48  tff(c_181, plain, (![A_87, B_88]: (r1_tarski('#skF_3'(A_87, B_88), B_88) | v2_tex_2(B_88, A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.04/1.48  tff(c_264, plain, (![A_97]: (r1_tarski('#skF_3'(A_97, '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', A_97) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_54, c_181])).
% 3.04/1.48  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.04/1.48  tff(c_267, plain, (![A_97]: (k3_xboole_0('#skF_3'(A_97, '#skF_5'), '#skF_5')='#skF_3'(A_97, '#skF_5') | v2_tex_2('#skF_5', A_97) | ~l1_pre_topc(A_97))), inference(resolution, [status(thm)], [c_264, c_8])).
% 3.04/1.48  tff(c_270, plain, (![A_98]: ('#skF_3'(A_98, '#skF_5')='#skF_5' | v2_tex_2('#skF_5', A_98) | ~l1_pre_topc(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_267])).
% 3.04/1.48  tff(c_36, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.04/1.48  tff(c_273, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_270, c_36])).
% 3.04/1.48  tff(c_276, plain, ('#skF_3'('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_273])).
% 3.04/1.48  tff(c_148, plain, (![B_82, A_83]: (v4_pre_topc(B_82, A_83) | ~v1_xboole_0(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.04/1.48  tff(c_156, plain, (![A_83]: (v4_pre_topc('#skF_5', A_83) | ~v1_xboole_0('#skF_5') | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83))), inference(resolution, [status(thm)], [c_54, c_148])).
% 3.04/1.48  tff(c_160, plain, (![A_83]: (v4_pre_topc('#skF_5', A_83) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_156])).
% 3.04/1.48  tff(c_214, plain, (![A_17, B_75]: (k9_subset_1(A_17, B_75, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_107])).
% 3.04/1.48  tff(c_533, plain, (![A_140, B_141, D_142]: (k9_subset_1(u1_struct_0(A_140), B_141, D_142)!='#skF_3'(A_140, B_141) | ~v4_pre_topc(D_142, A_140) | ~m1_subset_1(D_142, k1_zfmisc_1(u1_struct_0(A_140))) | v2_tex_2(B_141, A_140) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.04/1.48  tff(c_536, plain, (![A_140, B_75]: ('#skF_3'(A_140, B_75)!='#skF_5' | ~v4_pre_topc('#skF_5', A_140) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_140))) | v2_tex_2(B_75, A_140) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(superposition, [status(thm), theory('equality')], [c_214, c_533])).
% 3.04/1.48  tff(c_757, plain, (![A_162, B_163]: ('#skF_3'(A_162, B_163)!='#skF_5' | ~v4_pre_topc('#skF_5', A_162) | v2_tex_2(B_163, A_162) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_536])).
% 3.04/1.48  tff(c_791, plain, (![A_164]: ('#skF_3'(A_164, '#skF_5')!='#skF_5' | ~v4_pre_topc('#skF_5', A_164) | v2_tex_2('#skF_5', A_164) | ~l1_pre_topc(A_164))), inference(resolution, [status(thm)], [c_54, c_757])).
% 3.04/1.48  tff(c_806, plain, (![A_168]: ('#skF_3'(A_168, '#skF_5')!='#skF_5' | v2_tex_2('#skF_5', A_168) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168))), inference(resolution, [status(thm)], [c_160, c_791])).
% 3.04/1.48  tff(c_809, plain, ('#skF_3'('#skF_4', '#skF_5')!='#skF_5' | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_806, c_36])).
% 3.04/1.48  tff(c_813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_276, c_809])).
% 3.04/1.48  tff(c_814, plain, (![A_85]: (~v1_xboole_0(A_85))), inference(splitRight, [status(thm)], [c_177])).
% 3.04/1.48  tff(c_817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_814, c_40])).
% 3.04/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.48  
% 3.04/1.48  Inference rules
% 3.04/1.48  ----------------------
% 3.04/1.48  #Ref     : 0
% 3.04/1.48  #Sup     : 176
% 3.04/1.48  #Fact    : 0
% 3.04/1.48  #Define  : 0
% 3.04/1.48  #Split   : 2
% 3.04/1.48  #Chain   : 0
% 3.04/1.48  #Close   : 0
% 3.04/1.48  
% 3.04/1.48  Ordering : KBO
% 3.04/1.48  
% 3.04/1.48  Simplification rules
% 3.04/1.48  ----------------------
% 3.04/1.48  #Subsume      : 25
% 3.04/1.48  #Demod        : 77
% 3.04/1.48  #Tautology    : 51
% 3.04/1.48  #SimpNegUnit  : 5
% 3.04/1.48  #BackRed      : 8
% 3.04/1.48  
% 3.04/1.48  #Partial instantiations: 0
% 3.04/1.48  #Strategies tried      : 1
% 3.04/1.48  
% 3.04/1.48  Timing (in seconds)
% 3.04/1.48  ----------------------
% 3.04/1.49  Preprocessing        : 0.33
% 3.04/1.49  Parsing              : 0.17
% 3.04/1.49  CNF conversion       : 0.02
% 3.04/1.49  Main loop            : 0.37
% 3.04/1.49  Inferencing          : 0.14
% 3.04/1.49  Reduction            : 0.10
% 3.04/1.49  Demodulation         : 0.07
% 3.04/1.49  BG Simplification    : 0.02
% 3.04/1.49  Subsumption          : 0.08
% 3.04/1.49  Abstraction          : 0.02
% 3.04/1.49  MUC search           : 0.00
% 3.04/1.49  Cooper               : 0.00
% 3.04/1.49  Total                : 0.73
% 3.04/1.49  Index Insertion      : 0.00
% 3.04/1.49  Index Deletion       : 0.00
% 3.04/1.49  Index Matching       : 0.00
% 3.04/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
