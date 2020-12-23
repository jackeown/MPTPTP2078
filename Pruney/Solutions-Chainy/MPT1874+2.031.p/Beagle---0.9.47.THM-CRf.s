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
% DateTime   : Thu Dec  3 10:29:41 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 150 expanded)
%              Number of leaves         :   30 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 423 expanded)
%              Number of equality atoms :   14 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_88,axiom,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_47,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_98,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ r2_hidden(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_107,plain,
    ( m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_98])).

tff(c_112,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_107])).

tff(c_165,plain,(
    ! [A_59,B_60] :
      ( k6_domain_1(A_59,B_60) = k1_tarski(B_60)
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_171,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_112,c_165])).

tff(c_187,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_171])).

tff(c_223,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k6_domain_1(A_63,B_64),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_246,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_223])).

tff(c_258,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_246])).

tff(c_259,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_258])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_273,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_259,c_14])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_57,plain,(
    ! [B_33,A_34] :
      ( v1_xboole_0(B_33)
      | ~ m1_subset_1(B_33,A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_67,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_68,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_183,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_165])).

tff(c_195,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_183])).

tff(c_243,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_223])).

tff(c_255,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_243])).

tff(c_256,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_255])).

tff(c_785,plain,(
    ! [A_80,B_81,C_82] :
      ( k9_subset_1(u1_struct_0(A_80),B_81,k2_pre_topc(A_80,C_82)) = C_82
      | ~ r1_tarski(C_82,B_81)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ v2_tex_2(B_81,A_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_789,plain,(
    ! [B_81] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_81,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_81)
      | ~ v2_tex_2(B_81,'#skF_3')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_256,c_785])).

tff(c_807,plain,(
    ! [B_81] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_81,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_81)
      | ~ v2_tex_2(B_81,'#skF_3')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_789])).

tff(c_1178,plain,(
    ! [B_91] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_91,k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) = k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski('#skF_5'),B_91)
      | ~ v2_tex_2(B_91,'#skF_3')
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_807])).

tff(c_32,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_200,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_195,c_32])).

tff(c_1184,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_200])).

tff(c_1192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_273,c_1184])).

tff(c_1194,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_1244,plain,(
    ! [C_102,B_103,A_104] :
      ( ~ v1_xboole_0(C_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(C_102))
      | ~ r2_hidden(A_104,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1251,plain,(
    ! [A_104] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_104,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_1244])).

tff(c_1256,plain,(
    ! [A_104] : ~ r2_hidden(A_104,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_1251])).

tff(c_1258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1256,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:49:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.48  
% 3.26/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.48  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.26/1.48  
% 3.26/1.48  %Foreground sorts:
% 3.26/1.48  
% 3.26/1.48  
% 3.26/1.48  %Background operators:
% 3.26/1.48  
% 3.26/1.48  
% 3.26/1.48  %Foreground operators:
% 3.26/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.26/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.26/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.26/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.26/1.48  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.26/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.48  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.26/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.26/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.26/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.26/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.26/1.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.26/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.48  
% 3.26/1.49  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 3.26/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.26/1.49  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.26/1.49  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.26/1.49  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.26/1.49  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.26/1.49  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 3.26/1.49  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.26/1.49  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.49  tff(c_38, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.49  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.49  tff(c_47, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.49  tff(c_51, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_47])).
% 3.26/1.49  tff(c_98, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~r2_hidden(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.26/1.49  tff(c_107, plain, (m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_98])).
% 3.26/1.49  tff(c_112, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_51, c_107])).
% 3.26/1.49  tff(c_165, plain, (![A_59, B_60]: (k6_domain_1(A_59, B_60)=k1_tarski(B_60) | ~m1_subset_1(B_60, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.26/1.49  tff(c_171, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_112, c_165])).
% 3.26/1.49  tff(c_187, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_51, c_171])).
% 3.26/1.49  tff(c_223, plain, (![A_63, B_64]: (m1_subset_1(k6_domain_1(A_63, B_64), k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.26/1.49  tff(c_246, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_187, c_223])).
% 3.26/1.49  tff(c_258, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_246])).
% 3.26/1.49  tff(c_259, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_51, c_258])).
% 3.26/1.49  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.26/1.49  tff(c_273, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_259, c_14])).
% 3.26/1.49  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.49  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.49  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.49  tff(c_36, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.49  tff(c_57, plain, (![B_33, A_34]: (v1_xboole_0(B_33) | ~m1_subset_1(B_33, A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.26/1.49  tff(c_67, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_57])).
% 3.26/1.49  tff(c_68, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_67])).
% 3.26/1.49  tff(c_183, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_165])).
% 3.26/1.49  tff(c_195, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_183])).
% 3.26/1.49  tff(c_243, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_223])).
% 3.26/1.49  tff(c_255, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_243])).
% 3.26/1.49  tff(c_256, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_68, c_255])).
% 3.26/1.49  tff(c_785, plain, (![A_80, B_81, C_82]: (k9_subset_1(u1_struct_0(A_80), B_81, k2_pre_topc(A_80, C_82))=C_82 | ~r1_tarski(C_82, B_81) | ~m1_subset_1(C_82, k1_zfmisc_1(u1_struct_0(A_80))) | ~v2_tex_2(B_81, A_80) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.26/1.49  tff(c_789, plain, (![B_81]: (k9_subset_1(u1_struct_0('#skF_3'), B_81, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_81) | ~v2_tex_2(B_81, '#skF_3') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_256, c_785])).
% 3.26/1.49  tff(c_807, plain, (![B_81]: (k9_subset_1(u1_struct_0('#skF_3'), B_81, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_81) | ~v2_tex_2(B_81, '#skF_3') | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_789])).
% 3.26/1.49  tff(c_1178, plain, (![B_91]: (k9_subset_1(u1_struct_0('#skF_3'), B_91, k2_pre_topc('#skF_3', k1_tarski('#skF_5')))=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski('#skF_5'), B_91) | ~v2_tex_2(B_91, '#skF_3') | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_807])).
% 3.26/1.49  tff(c_32, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.49  tff(c_200, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_195, c_32])).
% 3.26/1.49  tff(c_1184, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1178, c_200])).
% 3.26/1.49  tff(c_1192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_273, c_1184])).
% 3.26/1.49  tff(c_1194, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_67])).
% 3.26/1.49  tff(c_1244, plain, (![C_102, B_103, A_104]: (~v1_xboole_0(C_102) | ~m1_subset_1(B_103, k1_zfmisc_1(C_102)) | ~r2_hidden(A_104, B_103))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.26/1.49  tff(c_1251, plain, (![A_104]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_104, '#skF_4'))), inference(resolution, [status(thm)], [c_40, c_1244])).
% 3.26/1.49  tff(c_1256, plain, (![A_104]: (~r2_hidden(A_104, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_1251])).
% 3.26/1.49  tff(c_1258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1256, c_34])).
% 3.26/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.49  
% 3.26/1.49  Inference rules
% 3.26/1.49  ----------------------
% 3.26/1.49  #Ref     : 0
% 3.26/1.49  #Sup     : 254
% 3.26/1.49  #Fact    : 0
% 3.26/1.49  #Define  : 0
% 3.26/1.49  #Split   : 8
% 3.26/1.49  #Chain   : 0
% 3.26/1.49  #Close   : 0
% 3.26/1.49  
% 3.26/1.49  Ordering : KBO
% 3.26/1.49  
% 3.26/1.49  Simplification rules
% 3.26/1.49  ----------------------
% 3.26/1.49  #Subsume      : 40
% 3.26/1.49  #Demod        : 90
% 3.26/1.49  #Tautology    : 96
% 3.26/1.49  #SimpNegUnit  : 92
% 3.26/1.49  #BackRed      : 2
% 3.26/1.49  
% 3.26/1.49  #Partial instantiations: 0
% 3.26/1.49  #Strategies tried      : 1
% 3.26/1.49  
% 3.26/1.49  Timing (in seconds)
% 3.26/1.49  ----------------------
% 3.26/1.49  Preprocessing        : 0.31
% 3.26/1.50  Parsing              : 0.16
% 3.26/1.50  CNF conversion       : 0.02
% 3.26/1.50  Main loop            : 0.43
% 3.26/1.50  Inferencing          : 0.16
% 3.26/1.50  Reduction            : 0.14
% 3.26/1.50  Demodulation         : 0.09
% 3.26/1.50  BG Simplification    : 0.02
% 3.26/1.50  Subsumption          : 0.08
% 3.26/1.50  Abstraction          : 0.03
% 3.26/1.50  MUC search           : 0.00
% 3.26/1.50  Cooper               : 0.00
% 3.26/1.50  Total                : 0.76
% 3.26/1.50  Index Insertion      : 0.00
% 3.26/1.50  Index Deletion       : 0.00
% 3.26/1.50  Index Matching       : 0.00
% 3.26/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
