%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:37 EST 2020

% Result     : Theorem 5.07s
% Output     : CNFRefutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 127 expanded)
%              Number of leaves         :   34 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 322 expanded)
%              Number of equality atoms :   22 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

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
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r1_tarski(C,B)
                 => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,C)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_38,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k1_tarski(A_10),B_11)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_61,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_65,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_61])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_136,plain,(
    ! [C_63,B_64,A_65] :
      ( r2_hidden(C_63,B_64)
      | ~ r2_hidden(C_63,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_283,plain,(
    ! [A_89,B_90,B_91] :
      ( r2_hidden('#skF_2'(A_89,B_90),B_91)
      | ~ r1_tarski(A_89,B_91)
      | r1_tarski(A_89,B_90) ) ),
    inference(resolution,[status(thm)],[c_10,c_136])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1139,plain,(
    ! [A_162,B_163,B_164,B_165] :
      ( r2_hidden('#skF_2'(A_162,B_163),B_164)
      | ~ r1_tarski(B_165,B_164)
      | ~ r1_tarski(A_162,B_165)
      | r1_tarski(A_162,B_163) ) ),
    inference(resolution,[status(thm)],[c_283,c_6])).

tff(c_1182,plain,(
    ! [A_168,B_169] :
      ( r2_hidden('#skF_2'(A_168,B_169),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_168,'#skF_5')
      | r1_tarski(A_168,B_169) ) ),
    inference(resolution,[status(thm)],[c_65,c_1139])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1200,plain,(
    ! [A_168] :
      ( ~ r1_tarski(A_168,'#skF_5')
      | r1_tarski(A_168,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1182,c_8])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_234,plain,(
    ! [A_75,B_76,C_77] :
      ( k9_subset_1(A_75,B_76,C_77) = k3_xboole_0(B_76,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_240,plain,(
    ! [B_76] : k9_subset_1(u1_struct_0('#skF_4'),B_76,'#skF_5') = k3_xboole_0(B_76,'#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_234])).

tff(c_309,plain,(
    ! [A_95,C_96,B_97] :
      ( k9_subset_1(A_95,C_96,B_97) = k9_subset_1(A_95,B_97,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_313,plain,(
    ! [B_97] : k9_subset_1(u1_struct_0('#skF_4'),B_97,'#skF_5') = k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',B_97) ),
    inference(resolution,[status(thm)],[c_44,c_309])).

tff(c_316,plain,(
    ! [B_97] : k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',B_97) = k3_xboole_0(B_97,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_313])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1031,plain,(
    ! [A_151,B_152,C_153] :
      ( k9_subset_1(u1_struct_0(A_151),B_152,k2_pre_topc(A_151,C_153)) = C_153
      | ~ r1_tarski(C_153,B_152)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ v2_tex_2(B_152,A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2964,plain,(
    ! [A_247,B_248,A_249] :
      ( k9_subset_1(u1_struct_0(A_247),B_248,k2_pre_topc(A_247,A_249)) = A_249
      | ~ r1_tarski(A_249,B_248)
      | ~ v2_tex_2(B_248,A_247)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247)
      | ~ r1_tarski(A_249,u1_struct_0(A_247)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1031])).

tff(c_2971,plain,(
    ! [A_249] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_249)) = A_249
      | ~ r1_tarski(A_249,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_249,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_44,c_2964])).

tff(c_2976,plain,(
    ! [A_249] :
      ( k3_xboole_0(k2_pre_topc('#skF_4',A_249),'#skF_5') = A_249
      | ~ r1_tarski(A_249,'#skF_5')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_249,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_316,c_2971])).

tff(c_2978,plain,(
    ! [A_250] :
      ( k3_xboole_0(k2_pre_topc('#skF_4',A_250),'#skF_5') = A_250
      | ~ r1_tarski(A_250,'#skF_5')
      | ~ r1_tarski(A_250,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2976])).

tff(c_3017,plain,(
    ! [A_251] :
      ( k3_xboole_0(k2_pre_topc('#skF_4',A_251),'#skF_5') = A_251
      | ~ r1_tarski(A_251,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1200,c_2978])).

tff(c_51,plain,(
    ! [B_39,A_40] :
      ( ~ r2_hidden(B_39,A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_51])).

tff(c_78,plain,(
    ! [B_52,A_53] :
      ( v1_xboole_0(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_84,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_78])).

tff(c_88,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_84])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_214,plain,(
    ! [A_73,B_74] :
      ( k6_domain_1(A_73,B_74) = k1_tarski(B_74)
      | ~ m1_subset_1(B_74,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_223,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_214])).

tff(c_228,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_223])).

tff(c_36,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_229,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_228,c_36])).

tff(c_317,plain,(
    k3_xboole_0(k2_pre_topc('#skF_4',k1_tarski('#skF_6')),'#skF_5') != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_229])).

tff(c_3043,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3017,c_317])).

tff(c_3053,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_3043])).

tff(c_3058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_3053])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.07/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/2.13  
% 5.07/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/2.13  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 5.07/2.13  
% 5.07/2.13  %Foreground sorts:
% 5.07/2.13  
% 5.07/2.13  
% 5.07/2.13  %Background operators:
% 5.07/2.13  
% 5.07/2.13  
% 5.07/2.13  %Foreground operators:
% 5.07/2.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.07/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.07/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.07/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.07/2.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.07/2.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.07/2.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.07/2.13  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.07/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.07/2.13  tff('#skF_5', type, '#skF_5': $i).
% 5.07/2.13  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.07/2.13  tff('#skF_6', type, '#skF_6': $i).
% 5.07/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.07/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.07/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.07/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.07/2.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.07/2.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.07/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.07/2.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.07/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.07/2.13  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.07/2.13  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.07/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.07/2.13  
% 5.07/2.14  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 5.07/2.14  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.07/2.14  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.07/2.14  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.07/2.14  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.07/2.14  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 5.07/2.14  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 5.07/2.14  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.07/2.14  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.07/2.14  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.07/2.14  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.07/2.14  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k1_tarski(A_10), B_11) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.07/2.14  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.07/2.14  tff(c_61, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.07/2.14  tff(c_65, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_61])).
% 5.07/2.14  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.07/2.14  tff(c_136, plain, (![C_63, B_64, A_65]: (r2_hidden(C_63, B_64) | ~r2_hidden(C_63, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.07/2.14  tff(c_283, plain, (![A_89, B_90, B_91]: (r2_hidden('#skF_2'(A_89, B_90), B_91) | ~r1_tarski(A_89, B_91) | r1_tarski(A_89, B_90))), inference(resolution, [status(thm)], [c_10, c_136])).
% 5.07/2.14  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.07/2.14  tff(c_1139, plain, (![A_162, B_163, B_164, B_165]: (r2_hidden('#skF_2'(A_162, B_163), B_164) | ~r1_tarski(B_165, B_164) | ~r1_tarski(A_162, B_165) | r1_tarski(A_162, B_163))), inference(resolution, [status(thm)], [c_283, c_6])).
% 5.07/2.14  tff(c_1182, plain, (![A_168, B_169]: (r2_hidden('#skF_2'(A_168, B_169), u1_struct_0('#skF_4')) | ~r1_tarski(A_168, '#skF_5') | r1_tarski(A_168, B_169))), inference(resolution, [status(thm)], [c_65, c_1139])).
% 5.07/2.14  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.07/2.14  tff(c_1200, plain, (![A_168]: (~r1_tarski(A_168, '#skF_5') | r1_tarski(A_168, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1182, c_8])).
% 5.07/2.14  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.07/2.14  tff(c_48, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.07/2.14  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.07/2.14  tff(c_42, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.07/2.14  tff(c_234, plain, (![A_75, B_76, C_77]: (k9_subset_1(A_75, B_76, C_77)=k3_xboole_0(B_76, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.07/2.14  tff(c_240, plain, (![B_76]: (k9_subset_1(u1_struct_0('#skF_4'), B_76, '#skF_5')=k3_xboole_0(B_76, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_234])).
% 5.07/2.14  tff(c_309, plain, (![A_95, C_96, B_97]: (k9_subset_1(A_95, C_96, B_97)=k9_subset_1(A_95, B_97, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.07/2.14  tff(c_313, plain, (![B_97]: (k9_subset_1(u1_struct_0('#skF_4'), B_97, '#skF_5')=k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', B_97))), inference(resolution, [status(thm)], [c_44, c_309])).
% 5.07/2.14  tff(c_316, plain, (![B_97]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', B_97)=k3_xboole_0(B_97, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_240, c_313])).
% 5.07/2.14  tff(c_24, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.07/2.14  tff(c_1031, plain, (![A_151, B_152, C_153]: (k9_subset_1(u1_struct_0(A_151), B_152, k2_pre_topc(A_151, C_153))=C_153 | ~r1_tarski(C_153, B_152) | ~m1_subset_1(C_153, k1_zfmisc_1(u1_struct_0(A_151))) | ~v2_tex_2(B_152, A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.07/2.14  tff(c_2964, plain, (![A_247, B_248, A_249]: (k9_subset_1(u1_struct_0(A_247), B_248, k2_pre_topc(A_247, A_249))=A_249 | ~r1_tarski(A_249, B_248) | ~v2_tex_2(B_248, A_247) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | v2_struct_0(A_247) | ~r1_tarski(A_249, u1_struct_0(A_247)))), inference(resolution, [status(thm)], [c_24, c_1031])).
% 5.07/2.14  tff(c_2971, plain, (![A_249]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_249))=A_249 | ~r1_tarski(A_249, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_249, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_44, c_2964])).
% 5.07/2.14  tff(c_2976, plain, (![A_249]: (k3_xboole_0(k2_pre_topc('#skF_4', A_249), '#skF_5')=A_249 | ~r1_tarski(A_249, '#skF_5') | v2_struct_0('#skF_4') | ~r1_tarski(A_249, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_316, c_2971])).
% 5.07/2.14  tff(c_2978, plain, (![A_250]: (k3_xboole_0(k2_pre_topc('#skF_4', A_250), '#skF_5')=A_250 | ~r1_tarski(A_250, '#skF_5') | ~r1_tarski(A_250, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_2976])).
% 5.07/2.14  tff(c_3017, plain, (![A_251]: (k3_xboole_0(k2_pre_topc('#skF_4', A_251), '#skF_5')=A_251 | ~r1_tarski(A_251, '#skF_5'))), inference(resolution, [status(thm)], [c_1200, c_2978])).
% 5.07/2.14  tff(c_51, plain, (![B_39, A_40]: (~r2_hidden(B_39, A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.07/2.14  tff(c_55, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_51])).
% 5.07/2.14  tff(c_78, plain, (![B_52, A_53]: (v1_xboole_0(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.07/2.14  tff(c_84, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_78])).
% 5.07/2.14  tff(c_88, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_55, c_84])).
% 5.07/2.14  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.07/2.14  tff(c_214, plain, (![A_73, B_74]: (k6_domain_1(A_73, B_74)=k1_tarski(B_74) | ~m1_subset_1(B_74, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.07/2.14  tff(c_223, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_214])).
% 5.07/2.14  tff(c_228, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_88, c_223])).
% 5.07/2.14  tff(c_36, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.07/2.14  tff(c_229, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_228, c_228, c_36])).
% 5.07/2.14  tff(c_317, plain, (k3_xboole_0(k2_pre_topc('#skF_4', k1_tarski('#skF_6')), '#skF_5')!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_229])).
% 5.07/2.14  tff(c_3043, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3017, c_317])).
% 5.07/2.14  tff(c_3053, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_14, c_3043])).
% 5.07/2.14  tff(c_3058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_3053])).
% 5.07/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.07/2.14  
% 5.07/2.14  Inference rules
% 5.07/2.14  ----------------------
% 5.07/2.14  #Ref     : 0
% 5.07/2.14  #Sup     : 715
% 5.07/2.14  #Fact    : 0
% 5.07/2.14  #Define  : 0
% 5.07/2.14  #Split   : 4
% 5.07/2.14  #Chain   : 0
% 5.07/2.14  #Close   : 0
% 5.07/2.14  
% 5.07/2.14  Ordering : KBO
% 5.07/2.14  
% 5.07/2.14  Simplification rules
% 5.07/2.14  ----------------------
% 5.07/2.14  #Subsume      : 144
% 5.07/2.14  #Demod        : 158
% 5.07/2.14  #Tautology    : 207
% 5.07/2.14  #SimpNegUnit  : 30
% 5.07/2.14  #BackRed      : 4
% 5.07/2.14  
% 5.07/2.14  #Partial instantiations: 0
% 5.07/2.14  #Strategies tried      : 1
% 5.07/2.14  
% 5.07/2.14  Timing (in seconds)
% 5.07/2.14  ----------------------
% 5.07/2.15  Preprocessing        : 0.46
% 5.07/2.15  Parsing              : 0.27
% 5.07/2.15  CNF conversion       : 0.03
% 5.07/2.15  Main loop            : 0.84
% 5.07/2.15  Inferencing          : 0.29
% 5.07/2.15  Reduction            : 0.26
% 5.07/2.15  Demodulation         : 0.17
% 5.07/2.15  BG Simplification    : 0.04
% 5.07/2.15  Subsumption          : 0.18
% 5.07/2.15  Abstraction          : 0.04
% 5.07/2.15  MUC search           : 0.00
% 5.07/2.15  Cooper               : 0.00
% 5.07/2.15  Total                : 1.33
% 5.07/2.15  Index Insertion      : 0.00
% 5.07/2.15  Index Deletion       : 0.00
% 5.07/2.15  Index Matching       : 0.00
% 5.07/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
