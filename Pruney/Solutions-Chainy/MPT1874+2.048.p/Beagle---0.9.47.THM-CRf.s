%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:43 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 155 expanded)
%              Number of leaves         :   30 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  141 ( 404 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_95,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k1_tarski(A_7),B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_275,plain,(
    ! [A_76,B_77,B_78] :
      ( r2_hidden('#skF_1'(A_76,B_77),B_78)
      | ~ r1_tarski(A_76,B_78)
      | r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_324,plain,(
    ! [A_87,B_88,B_89,B_90] :
      ( r2_hidden('#skF_1'(A_87,B_88),B_89)
      | ~ r1_tarski(B_90,B_89)
      | ~ r1_tarski(A_87,B_90)
      | r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_275,c_2])).

tff(c_497,plain,(
    ! [A_106,B_107,B_108,A_109] :
      ( r2_hidden('#skF_1'(A_106,B_107),B_108)
      | ~ r1_tarski(A_106,k1_tarski(A_109))
      | r1_tarski(A_106,B_107)
      | ~ r2_hidden(A_109,B_108) ) ),
    inference(resolution,[status(thm)],[c_12,c_324])).

tff(c_712,plain,(
    ! [A_138,B_139,B_140,A_141] :
      ( r2_hidden('#skF_1'(k1_tarski(A_138),B_139),B_140)
      | r1_tarski(k1_tarski(A_138),B_139)
      | ~ r2_hidden(A_141,B_140)
      | ~ r2_hidden(A_138,k1_tarski(A_141)) ) ),
    inference(resolution,[status(thm)],[c_12,c_497])).

tff(c_752,plain,(
    ! [A_142,B_143] :
      ( r2_hidden('#skF_1'(k1_tarski(A_142),B_143),'#skF_4')
      | r1_tarski(k1_tarski(A_142),B_143)
      | ~ r2_hidden(A_142,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_32,c_712])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_776,plain,(
    ! [A_144] :
      ( r1_tarski(k1_tarski(A_144),'#skF_4')
      | ~ r2_hidden(A_144,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_752,c_4])).

tff(c_940,plain,(
    ! [B_151] :
      ( r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_5'),B_151)),'#skF_4')
      | r1_tarski(k1_tarski('#skF_5'),B_151) ) ),
    inference(resolution,[status(thm)],[c_6,c_776])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_61,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_61])).

tff(c_337,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_1'(A_91,B_92),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_91,'#skF_4')
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_69,c_324])).

tff(c_353,plain,(
    ! [A_93] :
      ( ~ r1_tarski(A_93,'#skF_4')
      | r1_tarski(A_93,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_337,c_4])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | ~ r1_tarski(k1_tarski(A_7),B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_414,plain,(
    ! [A_97] :
      ( r2_hidden(A_97,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(A_97),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_353,c_10])).

tff(c_429,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski('#skF_1'(A_1,u1_struct_0('#skF_3'))),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_414,c_4])).

tff(c_972,plain,(
    r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_940,c_429])).

tff(c_71,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden('#skF_1'(A_41,B_42),B_42)
      | r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_43] : r1_tarski(A_43,A_43) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_82,plain,(
    ! [A_7] : r2_hidden(A_7,k1_tarski(A_7)) ),
    inference(resolution,[status(thm)],[c_77,c_10])).

tff(c_810,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_776])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_36,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_812,plain,(
    ! [A_145,B_146,C_147] :
      ( k9_subset_1(u1_struct_0(A_145),B_146,k2_pre_topc(A_145,C_147)) = C_147
      | ~ r1_tarski(C_147,B_146)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ v2_tex_2(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2434,plain,(
    ! [A_238,B_239,A_240] :
      ( k9_subset_1(u1_struct_0(A_238),B_239,k2_pre_topc(A_238,A_240)) = A_240
      | ~ r1_tarski(A_240,B_239)
      | ~ v2_tex_2(B_239,A_238)
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0(A_238)))
      | ~ l1_pre_topc(A_238)
      | ~ v2_pre_topc(A_238)
      | v2_struct_0(A_238)
      | ~ r1_tarski(A_240,u1_struct_0(A_238)) ) ),
    inference(resolution,[status(thm)],[c_16,c_812])).

tff(c_2441,plain,(
    ! [A_240] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_240)) = A_240
      | ~ r1_tarski(A_240,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_240,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_2434])).

tff(c_2446,plain,(
    ! [A_240] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_240)) = A_240
      | ~ r1_tarski(A_240,'#skF_4')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_240,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_36,c_2441])).

tff(c_2448,plain,(
    ! [A_241] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_241)) = A_241
      | ~ r1_tarski(A_241,'#skF_4')
      | ~ r1_tarski(A_241,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2446])).

tff(c_84,plain,(
    ! [C_45,B_46,A_47] :
      ( ~ v1_xboole_0(C_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(C_45))
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_47,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_84])).

tff(c_91,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_237,plain,(
    ! [A_71,B_72] :
      ( k6_domain_1(A_71,B_72) = k1_tarski(B_72)
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_246,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_237])).

tff(c_251,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_246])).

tff(c_30,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_252,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_251,c_30])).

tff(c_2465,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2448,c_252])).

tff(c_2490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_972,c_810,c_2465])).

tff(c_2491,plain,(
    ! [A_47] : ~ r2_hidden(A_47,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_2494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2491,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.86  
% 4.59/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.87  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.59/1.87  
% 4.59/1.87  %Foreground sorts:
% 4.59/1.87  
% 4.59/1.87  
% 4.59/1.87  %Background operators:
% 4.59/1.87  
% 4.59/1.87  
% 4.59/1.87  %Foreground operators:
% 4.59/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.59/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.59/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.59/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.59/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.59/1.87  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.59/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.59/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.59/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.59/1.87  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.59/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.59/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.59/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.59/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.59/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.59/1.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.59/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.59/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.59/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.59/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.59/1.87  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.59/1.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.59/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.59/1.87  
% 4.59/1.88  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.59/1.88  tff(f_95, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 4.59/1.88  tff(f_38, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.59/1.88  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.59/1.88  tff(f_75, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 4.59/1.88  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.59/1.88  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.59/1.88  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.88  tff(c_32, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.59/1.88  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k1_tarski(A_7), B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.59/1.88  tff(c_122, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.88  tff(c_275, plain, (![A_76, B_77, B_78]: (r2_hidden('#skF_1'(A_76, B_77), B_78) | ~r1_tarski(A_76, B_78) | r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_6, c_122])).
% 4.59/1.88  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.88  tff(c_324, plain, (![A_87, B_88, B_89, B_90]: (r2_hidden('#skF_1'(A_87, B_88), B_89) | ~r1_tarski(B_90, B_89) | ~r1_tarski(A_87, B_90) | r1_tarski(A_87, B_88))), inference(resolution, [status(thm)], [c_275, c_2])).
% 4.59/1.88  tff(c_497, plain, (![A_106, B_107, B_108, A_109]: (r2_hidden('#skF_1'(A_106, B_107), B_108) | ~r1_tarski(A_106, k1_tarski(A_109)) | r1_tarski(A_106, B_107) | ~r2_hidden(A_109, B_108))), inference(resolution, [status(thm)], [c_12, c_324])).
% 4.59/1.88  tff(c_712, plain, (![A_138, B_139, B_140, A_141]: (r2_hidden('#skF_1'(k1_tarski(A_138), B_139), B_140) | r1_tarski(k1_tarski(A_138), B_139) | ~r2_hidden(A_141, B_140) | ~r2_hidden(A_138, k1_tarski(A_141)))), inference(resolution, [status(thm)], [c_12, c_497])).
% 4.59/1.88  tff(c_752, plain, (![A_142, B_143]: (r2_hidden('#skF_1'(k1_tarski(A_142), B_143), '#skF_4') | r1_tarski(k1_tarski(A_142), B_143) | ~r2_hidden(A_142, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_32, c_712])).
% 4.59/1.88  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.88  tff(c_776, plain, (![A_144]: (r1_tarski(k1_tarski(A_144), '#skF_4') | ~r2_hidden(A_144, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_752, c_4])).
% 4.59/1.88  tff(c_940, plain, (![B_151]: (r1_tarski(k1_tarski('#skF_1'(k1_tarski('#skF_5'), B_151)), '#skF_4') | r1_tarski(k1_tarski('#skF_5'), B_151))), inference(resolution, [status(thm)], [c_6, c_776])).
% 4.59/1.88  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.59/1.88  tff(c_61, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.59/1.88  tff(c_69, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_61])).
% 4.59/1.88  tff(c_337, plain, (![A_91, B_92]: (r2_hidden('#skF_1'(A_91, B_92), u1_struct_0('#skF_3')) | ~r1_tarski(A_91, '#skF_4') | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_69, c_324])).
% 4.59/1.88  tff(c_353, plain, (![A_93]: (~r1_tarski(A_93, '#skF_4') | r1_tarski(A_93, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_337, c_4])).
% 4.59/1.88  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | ~r1_tarski(k1_tarski(A_7), B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.59/1.88  tff(c_414, plain, (![A_97]: (r2_hidden(A_97, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(A_97), '#skF_4'))), inference(resolution, [status(thm)], [c_353, c_10])).
% 4.59/1.88  tff(c_429, plain, (![A_1]: (r1_tarski(A_1, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski('#skF_1'(A_1, u1_struct_0('#skF_3'))), '#skF_4'))), inference(resolution, [status(thm)], [c_414, c_4])).
% 4.59/1.88  tff(c_972, plain, (r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_940, c_429])).
% 4.59/1.88  tff(c_71, plain, (![A_41, B_42]: (~r2_hidden('#skF_1'(A_41, B_42), B_42) | r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.59/1.88  tff(c_77, plain, (![A_43]: (r1_tarski(A_43, A_43))), inference(resolution, [status(thm)], [c_6, c_71])).
% 4.59/1.88  tff(c_82, plain, (![A_7]: (r2_hidden(A_7, k1_tarski(A_7)))), inference(resolution, [status(thm)], [c_77, c_10])).
% 4.59/1.88  tff(c_810, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_82, c_776])).
% 4.59/1.88  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.59/1.88  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.59/1.88  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.59/1.88  tff(c_36, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.59/1.88  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.59/1.88  tff(c_812, plain, (![A_145, B_146, C_147]: (k9_subset_1(u1_struct_0(A_145), B_146, k2_pre_topc(A_145, C_147))=C_147 | ~r1_tarski(C_147, B_146) | ~m1_subset_1(C_147, k1_zfmisc_1(u1_struct_0(A_145))) | ~v2_tex_2(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.59/1.88  tff(c_2434, plain, (![A_238, B_239, A_240]: (k9_subset_1(u1_struct_0(A_238), B_239, k2_pre_topc(A_238, A_240))=A_240 | ~r1_tarski(A_240, B_239) | ~v2_tex_2(B_239, A_238) | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0(A_238))) | ~l1_pre_topc(A_238) | ~v2_pre_topc(A_238) | v2_struct_0(A_238) | ~r1_tarski(A_240, u1_struct_0(A_238)))), inference(resolution, [status(thm)], [c_16, c_812])).
% 4.59/1.88  tff(c_2441, plain, (![A_240]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_240))=A_240 | ~r1_tarski(A_240, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_240, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_38, c_2434])).
% 4.59/1.88  tff(c_2446, plain, (![A_240]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_240))=A_240 | ~r1_tarski(A_240, '#skF_4') | v2_struct_0('#skF_3') | ~r1_tarski(A_240, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_36, c_2441])).
% 4.59/1.88  tff(c_2448, plain, (![A_241]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_241))=A_241 | ~r1_tarski(A_241, '#skF_4') | ~r1_tarski(A_241, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_44, c_2446])).
% 4.59/1.88  tff(c_84, plain, (![C_45, B_46, A_47]: (~v1_xboole_0(C_45) | ~m1_subset_1(B_46, k1_zfmisc_1(C_45)) | ~r2_hidden(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.59/1.88  tff(c_90, plain, (![A_47]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_47, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_84])).
% 4.59/1.88  tff(c_91, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_90])).
% 4.59/1.88  tff(c_34, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.59/1.88  tff(c_237, plain, (![A_71, B_72]: (k6_domain_1(A_71, B_72)=k1_tarski(B_72) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.59/1.88  tff(c_246, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_237])).
% 4.59/1.88  tff(c_251, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_91, c_246])).
% 4.59/1.88  tff(c_30, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.59/1.88  tff(c_252, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_251, c_30])).
% 4.59/1.88  tff(c_2465, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2448, c_252])).
% 4.59/1.88  tff(c_2490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_972, c_810, c_2465])).
% 4.59/1.88  tff(c_2491, plain, (![A_47]: (~r2_hidden(A_47, '#skF_4'))), inference(splitRight, [status(thm)], [c_90])).
% 4.59/1.88  tff(c_2494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2491, c_32])).
% 4.59/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.88  
% 4.59/1.88  Inference rules
% 4.59/1.88  ----------------------
% 4.59/1.88  #Ref     : 0
% 4.59/1.88  #Sup     : 621
% 4.59/1.88  #Fact    : 0
% 4.59/1.88  #Define  : 0
% 4.59/1.88  #Split   : 5
% 4.59/1.88  #Chain   : 0
% 4.59/1.88  #Close   : 0
% 4.59/1.88  
% 4.59/1.88  Ordering : KBO
% 4.59/1.88  
% 4.59/1.88  Simplification rules
% 4.59/1.88  ----------------------
% 4.59/1.88  #Subsume      : 320
% 4.59/1.88  #Demod        : 86
% 4.59/1.88  #Tautology    : 58
% 4.59/1.88  #SimpNegUnit  : 8
% 4.59/1.88  #BackRed      : 2
% 4.59/1.88  
% 4.59/1.88  #Partial instantiations: 0
% 4.59/1.88  #Strategies tried      : 1
% 4.59/1.88  
% 4.59/1.88  Timing (in seconds)
% 4.59/1.88  ----------------------
% 4.59/1.89  Preprocessing        : 0.32
% 4.59/1.89  Parsing              : 0.17
% 4.59/1.89  CNF conversion       : 0.02
% 4.59/1.89  Main loop            : 0.74
% 4.59/1.89  Inferencing          : 0.23
% 4.59/1.89  Reduction            : 0.20
% 4.59/1.89  Demodulation         : 0.14
% 4.59/1.89  BG Simplification    : 0.02
% 4.59/1.89  Subsumption          : 0.23
% 4.59/1.89  Abstraction          : 0.03
% 4.59/1.89  MUC search           : 0.00
% 4.59/1.89  Cooper               : 0.00
% 4.59/1.89  Total                : 1.09
% 4.59/1.89  Index Insertion      : 0.00
% 4.59/1.89  Index Deletion       : 0.00
% 4.59/1.89  Index Matching       : 0.00
% 4.59/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
