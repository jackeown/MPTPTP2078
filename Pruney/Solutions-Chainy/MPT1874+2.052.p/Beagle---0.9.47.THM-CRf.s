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
% DateTime   : Thu Dec  3 10:29:44 EST 2020

% Result     : Theorem 5.36s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 138 expanded)
%              Number of leaves         :   36 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  141 ( 342 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_84,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k1_tarski(A_66),k1_zfmisc_1(B_67))
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_88,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k1_tarski(A_66),B_67)
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_84,c_24])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_68,B_69] :
      ( ~ r2_hidden('#skF_1'(A_68,B_69),B_69)
      | r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_64,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_64])).

tff(c_97,plain,(
    ! [C_73,B_74,A_75] :
      ( r2_hidden(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_309,plain,(
    ! [A_119,B_120,B_121] :
      ( r2_hidden('#skF_1'(A_119,B_120),B_121)
      | ~ r1_tarski(A_119,B_121)
      | r1_tarski(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_396,plain,(
    ! [A_140,B_141,B_142,B_143] :
      ( r2_hidden('#skF_1'(A_140,B_141),B_142)
      | ~ r1_tarski(B_143,B_142)
      | ~ r1_tarski(A_140,B_143)
      | r1_tarski(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_309,c_2])).

tff(c_418,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_1'(A_151,B_152),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_151,'#skF_4')
      | r1_tarski(A_151,B_152) ) ),
    inference(resolution,[status(thm)],[c_68,c_396])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_439,plain,(
    ! [A_153] :
      ( ~ r1_tarski(A_153,'#skF_4')
      | r1_tarski(A_153,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_418,c_4])).

tff(c_329,plain,(
    ! [A_119,B_120,B_2,B_121] :
      ( r2_hidden('#skF_1'(A_119,B_120),B_2)
      | ~ r1_tarski(B_121,B_2)
      | ~ r1_tarski(A_119,B_121)
      | r1_tarski(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_309,c_2])).

tff(c_587,plain,(
    ! [A_172,B_173,A_174] :
      ( r2_hidden('#skF_1'(A_172,B_173),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_172,A_174)
      | r1_tarski(A_172,B_173)
      | ~ r1_tarski(A_174,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_439,c_329])).

tff(c_1041,plain,(
    ! [A_214,B_215,B_216] :
      ( r2_hidden('#skF_1'(k1_tarski(A_214),B_215),u1_struct_0('#skF_3'))
      | r1_tarski(k1_tarski(A_214),B_215)
      | ~ r1_tarski(B_216,'#skF_4')
      | ~ r2_hidden(A_214,B_216) ) ),
    inference(resolution,[status(thm)],[c_88,c_587])).

tff(c_1065,plain,(
    ! [B_215] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_5'),B_215),u1_struct_0('#skF_3'))
      | r1_tarski(k1_tarski('#skF_5'),B_215)
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_1041])).

tff(c_1082,plain,(
    ! [B_217] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_5'),B_217),u1_struct_0('#skF_3'))
      | r1_tarski(k1_tarski('#skF_5'),B_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1065])).

tff(c_1108,plain,(
    r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1082,c_4])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(A_36,k1_zfmisc_1(B_37))
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1161,plain,(
    ! [A_220,B_221,C_222] :
      ( k9_subset_1(u1_struct_0(A_220),B_221,k2_pre_topc(A_220,C_222)) = C_222
      | ~ r1_tarski(C_222,B_221)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ v2_tex_2(B_221,A_220)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2621,plain,(
    ! [A_343,B_344,A_345] :
      ( k9_subset_1(u1_struct_0(A_343),B_344,k2_pre_topc(A_343,A_345)) = A_345
      | ~ r1_tarski(A_345,B_344)
      | ~ v2_tex_2(B_344,A_343)
      | ~ m1_subset_1(B_344,k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343)
      | v2_struct_0(A_343)
      | ~ r1_tarski(A_345,u1_struct_0(A_343)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1161])).

tff(c_2631,plain,(
    ! [A_345] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_345)) = A_345
      | ~ r1_tarski(A_345,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_345,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_2621])).

tff(c_2637,plain,(
    ! [A_345] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_345)) = A_345
      | ~ r1_tarski(A_345,'#skF_4')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_345,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_2631])).

tff(c_2686,plain,(
    ! [A_348] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_348)) = A_348
      | ~ r1_tarski(A_348,'#skF_4')
      | ~ r1_tarski(A_348,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2637])).

tff(c_117,plain,(
    ! [C_80,B_81,A_82] :
      ( ~ v1_xboole_0(C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_126,plain,(
    ! [A_82] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_82,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_117])).

tff(c_127,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_138,plain,(
    ! [A_86,B_87] :
      ( k6_domain_1(A_86,B_87) = k1_tarski(B_87)
      | ~ m1_subset_1(B_87,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_150,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_138])).

tff(c_156,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_150])).

tff(c_40,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_167,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_156,c_40])).

tff(c_2703,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2686,c_167])).

tff(c_2727,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_2703])).

tff(c_2740,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_2727])).

tff(c_2745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2740])).

tff(c_2746,plain,(
    ! [A_82] : ~ r2_hidden(A_82,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_2749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2746,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n011.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 09:30:42 EST 2020
% 0.15/0.31  % CPUTime    : 
% 0.15/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.36/2.02  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.03  
% 5.36/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.03  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k9_subset_1 > k1_enumset1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.36/2.03  
% 5.36/2.03  %Foreground sorts:
% 5.36/2.03  
% 5.36/2.03  
% 5.36/2.03  %Background operators:
% 5.36/2.03  
% 5.36/2.03  
% 5.36/2.03  %Foreground operators:
% 5.36/2.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.36/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.36/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.36/2.03  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.36/2.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.36/2.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.36/2.03  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.36/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.36/2.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.36/2.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.36/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.36/2.03  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.36/2.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.36/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.36/2.03  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.36/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.36/2.03  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.36/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.36/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.36/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.36/2.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.36/2.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.36/2.03  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.36/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.36/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.36/2.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.36/2.03  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.36/2.03  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.36/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.36/2.03  
% 5.36/2.05  tff(f_107, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_tex_2)).
% 5.36/2.05  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 5.36/2.05  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.36/2.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.36/2.05  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tex_2)).
% 5.36/2.05  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 5.36/2.05  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.36/2.05  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.36/2.05  tff(c_84, plain, (![A_66, B_67]: (m1_subset_1(k1_tarski(A_66), k1_zfmisc_1(B_67)) | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.36/2.05  tff(c_24, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.36/2.05  tff(c_88, plain, (![A_66, B_67]: (r1_tarski(k1_tarski(A_66), B_67) | ~r2_hidden(A_66, B_67))), inference(resolution, [status(thm)], [c_84, c_24])).
% 5.36/2.05  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.36/2.05  tff(c_89, plain, (![A_68, B_69]: (~r2_hidden('#skF_1'(A_68, B_69), B_69) | r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.36/2.05  tff(c_94, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_89])).
% 5.36/2.05  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.36/2.05  tff(c_64, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.36/2.05  tff(c_68, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_64])).
% 5.36/2.05  tff(c_97, plain, (![C_73, B_74, A_75]: (r2_hidden(C_73, B_74) | ~r2_hidden(C_73, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.36/2.05  tff(c_309, plain, (![A_119, B_120, B_121]: (r2_hidden('#skF_1'(A_119, B_120), B_121) | ~r1_tarski(A_119, B_121) | r1_tarski(A_119, B_120))), inference(resolution, [status(thm)], [c_6, c_97])).
% 5.36/2.05  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.36/2.05  tff(c_396, plain, (![A_140, B_141, B_142, B_143]: (r2_hidden('#skF_1'(A_140, B_141), B_142) | ~r1_tarski(B_143, B_142) | ~r1_tarski(A_140, B_143) | r1_tarski(A_140, B_141))), inference(resolution, [status(thm)], [c_309, c_2])).
% 5.36/2.05  tff(c_418, plain, (![A_151, B_152]: (r2_hidden('#skF_1'(A_151, B_152), u1_struct_0('#skF_3')) | ~r1_tarski(A_151, '#skF_4') | r1_tarski(A_151, B_152))), inference(resolution, [status(thm)], [c_68, c_396])).
% 5.36/2.05  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.36/2.05  tff(c_439, plain, (![A_153]: (~r1_tarski(A_153, '#skF_4') | r1_tarski(A_153, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_418, c_4])).
% 5.36/2.05  tff(c_329, plain, (![A_119, B_120, B_2, B_121]: (r2_hidden('#skF_1'(A_119, B_120), B_2) | ~r1_tarski(B_121, B_2) | ~r1_tarski(A_119, B_121) | r1_tarski(A_119, B_120))), inference(resolution, [status(thm)], [c_309, c_2])).
% 5.36/2.05  tff(c_587, plain, (![A_172, B_173, A_174]: (r2_hidden('#skF_1'(A_172, B_173), u1_struct_0('#skF_3')) | ~r1_tarski(A_172, A_174) | r1_tarski(A_172, B_173) | ~r1_tarski(A_174, '#skF_4'))), inference(resolution, [status(thm)], [c_439, c_329])).
% 5.36/2.05  tff(c_1041, plain, (![A_214, B_215, B_216]: (r2_hidden('#skF_1'(k1_tarski(A_214), B_215), u1_struct_0('#skF_3')) | r1_tarski(k1_tarski(A_214), B_215) | ~r1_tarski(B_216, '#skF_4') | ~r2_hidden(A_214, B_216))), inference(resolution, [status(thm)], [c_88, c_587])).
% 5.36/2.05  tff(c_1065, plain, (![B_215]: (r2_hidden('#skF_1'(k1_tarski('#skF_5'), B_215), u1_struct_0('#skF_3')) | r1_tarski(k1_tarski('#skF_5'), B_215) | ~r1_tarski('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_1041])).
% 5.36/2.05  tff(c_1082, plain, (![B_217]: (r2_hidden('#skF_1'(k1_tarski('#skF_5'), B_217), u1_struct_0('#skF_3')) | r1_tarski(k1_tarski('#skF_5'), B_217))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1065])).
% 5.36/2.05  tff(c_1108, plain, (r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1082, c_4])).
% 5.36/2.05  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.36/2.05  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.36/2.05  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.36/2.05  tff(c_46, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.36/2.05  tff(c_26, plain, (![A_36, B_37]: (m1_subset_1(A_36, k1_zfmisc_1(B_37)) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.36/2.05  tff(c_1161, plain, (![A_220, B_221, C_222]: (k9_subset_1(u1_struct_0(A_220), B_221, k2_pre_topc(A_220, C_222))=C_222 | ~r1_tarski(C_222, B_221) | ~m1_subset_1(C_222, k1_zfmisc_1(u1_struct_0(A_220))) | ~v2_tex_2(B_221, A_220) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220) | ~v2_pre_topc(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.36/2.05  tff(c_2621, plain, (![A_343, B_344, A_345]: (k9_subset_1(u1_struct_0(A_343), B_344, k2_pre_topc(A_343, A_345))=A_345 | ~r1_tarski(A_345, B_344) | ~v2_tex_2(B_344, A_343) | ~m1_subset_1(B_344, k1_zfmisc_1(u1_struct_0(A_343))) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343) | v2_struct_0(A_343) | ~r1_tarski(A_345, u1_struct_0(A_343)))), inference(resolution, [status(thm)], [c_26, c_1161])).
% 5.36/2.05  tff(c_2631, plain, (![A_345]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_345))=A_345 | ~r1_tarski(A_345, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_345, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_2621])).
% 5.36/2.05  tff(c_2637, plain, (![A_345]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_345))=A_345 | ~r1_tarski(A_345, '#skF_4') | v2_struct_0('#skF_3') | ~r1_tarski(A_345, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_2631])).
% 5.36/2.05  tff(c_2686, plain, (![A_348]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_348))=A_348 | ~r1_tarski(A_348, '#skF_4') | ~r1_tarski(A_348, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_2637])).
% 5.36/2.05  tff(c_117, plain, (![C_80, B_81, A_82]: (~v1_xboole_0(C_80) | ~m1_subset_1(B_81, k1_zfmisc_1(C_80)) | ~r2_hidden(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.36/2.05  tff(c_126, plain, (![A_82]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_82, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_117])).
% 5.36/2.05  tff(c_127, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_126])).
% 5.36/2.05  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.36/2.05  tff(c_138, plain, (![A_86, B_87]: (k6_domain_1(A_86, B_87)=k1_tarski(B_87) | ~m1_subset_1(B_87, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.36/2.05  tff(c_150, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_138])).
% 5.36/2.05  tff(c_156, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_127, c_150])).
% 5.36/2.05  tff(c_40, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.36/2.05  tff(c_167, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_156, c_40])).
% 5.36/2.05  tff(c_2703, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2686, c_167])).
% 5.36/2.05  tff(c_2727, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_2703])).
% 5.36/2.05  tff(c_2740, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_2727])).
% 5.36/2.05  tff(c_2745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_2740])).
% 5.36/2.05  tff(c_2746, plain, (![A_82]: (~r2_hidden(A_82, '#skF_4'))), inference(splitRight, [status(thm)], [c_126])).
% 5.36/2.05  tff(c_2749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2746, c_42])).
% 5.36/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.05  
% 5.36/2.05  Inference rules
% 5.36/2.05  ----------------------
% 5.36/2.05  #Ref     : 0
% 5.36/2.05  #Sup     : 734
% 5.36/2.05  #Fact    : 0
% 5.36/2.05  #Define  : 0
% 5.36/2.05  #Split   : 7
% 5.36/2.05  #Chain   : 0
% 5.36/2.05  #Close   : 0
% 5.36/2.05  
% 5.36/2.05  Ordering : KBO
% 5.36/2.05  
% 5.36/2.05  Simplification rules
% 5.36/2.05  ----------------------
% 5.36/2.05  #Subsume      : 353
% 5.36/2.05  #Demod        : 68
% 5.36/2.05  #Tautology    : 59
% 5.36/2.05  #SimpNegUnit  : 8
% 5.36/2.05  #BackRed      : 2
% 5.36/2.05  
% 5.36/2.05  #Partial instantiations: 0
% 5.36/2.05  #Strategies tried      : 1
% 5.36/2.05  
% 5.36/2.05  Timing (in seconds)
% 5.36/2.05  ----------------------
% 5.36/2.05  Preprocessing        : 0.35
% 5.36/2.05  Parsing              : 0.19
% 5.36/2.05  CNF conversion       : 0.02
% 5.36/2.05  Main loop            : 0.91
% 5.36/2.05  Inferencing          : 0.27
% 5.36/2.05  Reduction            : 0.24
% 5.36/2.05  Demodulation         : 0.16
% 5.36/2.05  BG Simplification    : 0.03
% 5.36/2.05  Subsumption          : 0.31
% 5.36/2.05  Abstraction          : 0.04
% 5.36/2.05  MUC search           : 0.00
% 5.36/2.05  Cooper               : 0.00
% 5.36/2.05  Total                : 1.29
% 5.36/2.05  Index Insertion      : 0.00
% 5.36/2.05  Index Deletion       : 0.00
% 5.36/2.05  Index Matching       : 0.00
% 5.36/2.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
