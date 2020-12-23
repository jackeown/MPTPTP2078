%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:41 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 163 expanded)
%              Number of leaves         :   32 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 395 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_100,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_85,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_2'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_93,plain,(
    ! [A_48] : r1_tarski(A_48,A_48) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_95,plain,(
    ! [A_50] : r1_tarski(A_50,A_50) ),
    inference(resolution,[status(thm)],[c_85,c_8])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | ~ r1_tarski(k1_tarski(A_14),B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_100,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(resolution,[status(thm)],[c_95,c_16])).

tff(c_36,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_tarski(A_14),B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_113,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(A_55,C_56)
      | ~ r1_tarski(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_301,plain,(
    ! [A_77,B_78,A_79] :
      ( r1_tarski(A_77,B_78)
      | ~ r1_tarski(A_77,k1_tarski(A_79))
      | ~ r2_hidden(A_79,B_78) ) ),
    inference(resolution,[status(thm)],[c_18,c_113])).

tff(c_362,plain,(
    ! [A_89,B_90,A_91] :
      ( r1_tarski(k1_tarski(A_89),B_90)
      | ~ r2_hidden(A_91,B_90)
      | ~ r2_hidden(A_89,k1_tarski(A_91)) ) ),
    inference(resolution,[status(thm)],[c_18,c_301])).

tff(c_390,plain,(
    ! [A_92] :
      ( r1_tarski(k1_tarski(A_92),'#skF_5')
      | ~ r2_hidden(A_92,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_36,c_362])).

tff(c_418,plain,(
    r1_tarski(k1_tarski('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_390])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_70,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_78,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_126,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_58,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_78,c_113])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_tarski(A_10,C_12)
      | ~ r1_tarski(B_11,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_133,plain,(
    ! [A_10,A_58] :
      ( r1_tarski(A_10,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_10,A_58)
      | ~ r1_tarski(A_58,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_126,c_12])).

tff(c_424,plain,
    ( r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_418,c_133])).

tff(c_439,plain,(
    r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_424])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_948,plain,(
    ! [A_113,B_114,C_115] :
      ( k9_subset_1(u1_struct_0(A_113),B_114,k2_pre_topc(A_113,C_115)) = C_115
      | ~ r1_tarski(C_115,B_114)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ v2_tex_2(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2265,plain,(
    ! [A_166,B_167,A_168] :
      ( k9_subset_1(u1_struct_0(A_166),B_167,k2_pre_topc(A_166,A_168)) = A_168
      | ~ r1_tarski(A_168,B_167)
      | ~ v2_tex_2(B_167,A_166)
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166)
      | ~ r1_tarski(A_168,u1_struct_0(A_166)) ) ),
    inference(resolution,[status(thm)],[c_22,c_948])).

tff(c_2272,plain,(
    ! [A_168] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_168)) = A_168
      | ~ r1_tarski(A_168,'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_168,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_2265])).

tff(c_2277,plain,(
    ! [A_168] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_168)) = A_168
      | ~ r1_tarski(A_168,'#skF_5')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_168,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_2272])).

tff(c_2296,plain,(
    ! [A_171] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',A_171)) = A_171
      | ~ r1_tarski(A_171,'#skF_5')
      | ~ r1_tarski(A_171,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2277])).

tff(c_124,plain,(
    ! [A_55] :
      ( r1_tarski(A_55,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_55,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_78,c_113])).

tff(c_135,plain,(
    ! [C_59,B_60,A_61] :
      ( r2_hidden(C_59,B_60)
      | ~ r2_hidden(C_59,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_148,plain,(
    ! [B_62] :
      ( r2_hidden('#skF_6',B_62)
      | ~ r1_tarski('#skF_5',B_62) ) ),
    inference(resolution,[status(thm)],[c_36,c_135])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [B_63] :
      ( ~ v1_xboole_0(B_63)
      | ~ r1_tarski('#skF_5',B_63) ) ),
    inference(resolution,[status(thm)],[c_148,c_2])).

tff(c_160,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_124,c_156])).

tff(c_174,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_160])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_256,plain,(
    ! [A_74,B_75] :
      ( k6_domain_1(A_74,B_75) = k1_tarski(B_75)
      | ~ m1_subset_1(B_75,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_265,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_256])).

tff(c_270,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_265])).

tff(c_34,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k6_domain_1(u1_struct_0('#skF_4'),'#skF_6'))) != k6_domain_1(u1_struct_0('#skF_4'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_278,plain,(
    k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',k2_pre_topc('#skF_4',k1_tarski('#skF_6'))) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_270,c_34])).

tff(c_2309,plain,
    ( ~ r1_tarski(k1_tarski('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_tarski('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2296,c_278])).

tff(c_2327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_418,c_2309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:57:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.68  
% 4.07/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.68  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.07/1.68  
% 4.07/1.68  %Foreground sorts:
% 4.07/1.68  
% 4.07/1.68  
% 4.07/1.68  %Background operators:
% 4.07/1.68  
% 4.07/1.68  
% 4.07/1.68  %Foreground operators:
% 4.07/1.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.07/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.07/1.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.07/1.68  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.07/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.07/1.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.07/1.68  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.07/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.07/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.07/1.68  tff('#skF_5', type, '#skF_5': $i).
% 4.07/1.68  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.07/1.68  tff('#skF_6', type, '#skF_6': $i).
% 4.07/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.07/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/1.68  tff('#skF_4', type, '#skF_4': $i).
% 4.07/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/1.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.07/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.07/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.07/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.07/1.68  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.07/1.68  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.07/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.07/1.68  
% 4.07/1.69  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.07/1.69  tff(f_50, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.07/1.69  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 4.07/1.69  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.07/1.69  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.07/1.69  tff(f_80, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 4.07/1.69  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.07/1.69  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.07/1.69  tff(c_85, plain, (![A_48, B_49]: (r2_hidden('#skF_2'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.07/1.69  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.07/1.69  tff(c_93, plain, (![A_48]: (r1_tarski(A_48, A_48))), inference(resolution, [status(thm)], [c_85, c_8])).
% 4.07/1.69  tff(c_95, plain, (![A_50]: (r1_tarski(A_50, A_50))), inference(resolution, [status(thm)], [c_85, c_8])).
% 4.07/1.69  tff(c_16, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | ~r1_tarski(k1_tarski(A_14), B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.07/1.69  tff(c_100, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(resolution, [status(thm)], [c_95, c_16])).
% 4.07/1.69  tff(c_36, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.69  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.07/1.69  tff(c_113, plain, (![A_55, C_56, B_57]: (r1_tarski(A_55, C_56) | ~r1_tarski(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.07/1.69  tff(c_301, plain, (![A_77, B_78, A_79]: (r1_tarski(A_77, B_78) | ~r1_tarski(A_77, k1_tarski(A_79)) | ~r2_hidden(A_79, B_78))), inference(resolution, [status(thm)], [c_18, c_113])).
% 4.07/1.69  tff(c_362, plain, (![A_89, B_90, A_91]: (r1_tarski(k1_tarski(A_89), B_90) | ~r2_hidden(A_91, B_90) | ~r2_hidden(A_89, k1_tarski(A_91)))), inference(resolution, [status(thm)], [c_18, c_301])).
% 4.07/1.69  tff(c_390, plain, (![A_92]: (r1_tarski(k1_tarski(A_92), '#skF_5') | ~r2_hidden(A_92, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_36, c_362])).
% 4.07/1.69  tff(c_418, plain, (r1_tarski(k1_tarski('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_100, c_390])).
% 4.07/1.69  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.69  tff(c_70, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.07/1.69  tff(c_78, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_70])).
% 4.07/1.69  tff(c_126, plain, (![A_58]: (r1_tarski(A_58, u1_struct_0('#skF_4')) | ~r1_tarski(A_58, '#skF_5'))), inference(resolution, [status(thm)], [c_78, c_113])).
% 4.07/1.69  tff(c_12, plain, (![A_10, C_12, B_11]: (r1_tarski(A_10, C_12) | ~r1_tarski(B_11, C_12) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.07/1.69  tff(c_133, plain, (![A_10, A_58]: (r1_tarski(A_10, u1_struct_0('#skF_4')) | ~r1_tarski(A_10, A_58) | ~r1_tarski(A_58, '#skF_5'))), inference(resolution, [status(thm)], [c_126, c_12])).
% 4.07/1.69  tff(c_424, plain, (r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_418, c_133])).
% 4.07/1.69  tff(c_439, plain, (r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_424])).
% 4.07/1.69  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.69  tff(c_46, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.69  tff(c_44, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.69  tff(c_40, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.69  tff(c_22, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.07/1.69  tff(c_948, plain, (![A_113, B_114, C_115]: (k9_subset_1(u1_struct_0(A_113), B_114, k2_pre_topc(A_113, C_115))=C_115 | ~r1_tarski(C_115, B_114) | ~m1_subset_1(C_115, k1_zfmisc_1(u1_struct_0(A_113))) | ~v2_tex_2(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.07/1.69  tff(c_2265, plain, (![A_166, B_167, A_168]: (k9_subset_1(u1_struct_0(A_166), B_167, k2_pre_topc(A_166, A_168))=A_168 | ~r1_tarski(A_168, B_167) | ~v2_tex_2(B_167, A_166) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166) | ~r1_tarski(A_168, u1_struct_0(A_166)))), inference(resolution, [status(thm)], [c_22, c_948])).
% 4.07/1.69  tff(c_2272, plain, (![A_168]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_168))=A_168 | ~r1_tarski(A_168, '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_168, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_42, c_2265])).
% 4.07/1.69  tff(c_2277, plain, (![A_168]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_168))=A_168 | ~r1_tarski(A_168, '#skF_5') | v2_struct_0('#skF_4') | ~r1_tarski(A_168, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_2272])).
% 4.07/1.69  tff(c_2296, plain, (![A_171]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', A_171))=A_171 | ~r1_tarski(A_171, '#skF_5') | ~r1_tarski(A_171, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_2277])).
% 4.07/1.69  tff(c_124, plain, (![A_55]: (r1_tarski(A_55, u1_struct_0('#skF_4')) | ~r1_tarski(A_55, '#skF_5'))), inference(resolution, [status(thm)], [c_78, c_113])).
% 4.07/1.69  tff(c_135, plain, (![C_59, B_60, A_61]: (r2_hidden(C_59, B_60) | ~r2_hidden(C_59, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.07/1.69  tff(c_148, plain, (![B_62]: (r2_hidden('#skF_6', B_62) | ~r1_tarski('#skF_5', B_62))), inference(resolution, [status(thm)], [c_36, c_135])).
% 4.07/1.69  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.07/1.69  tff(c_156, plain, (![B_63]: (~v1_xboole_0(B_63) | ~r1_tarski('#skF_5', B_63))), inference(resolution, [status(thm)], [c_148, c_2])).
% 4.07/1.69  tff(c_160, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_124, c_156])).
% 4.07/1.69  tff(c_174, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_160])).
% 4.07/1.69  tff(c_38, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.69  tff(c_256, plain, (![A_74, B_75]: (k6_domain_1(A_74, B_75)=k1_tarski(B_75) | ~m1_subset_1(B_75, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.07/1.69  tff(c_265, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_256])).
% 4.07/1.69  tff(c_270, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_174, c_265])).
% 4.07/1.69  tff(c_34, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')))!=k6_domain_1(u1_struct_0('#skF_4'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.07/1.69  tff(c_278, plain, (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', k2_pre_topc('#skF_4', k1_tarski('#skF_6')))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_270, c_34])).
% 4.07/1.69  tff(c_2309, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_5') | ~r1_tarski(k1_tarski('#skF_6'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2296, c_278])).
% 4.07/1.69  tff(c_2327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_439, c_418, c_2309])).
% 4.07/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.69  
% 4.07/1.69  Inference rules
% 4.07/1.69  ----------------------
% 4.07/1.69  #Ref     : 0
% 4.07/1.69  #Sup     : 521
% 4.07/1.69  #Fact    : 0
% 4.07/1.69  #Define  : 0
% 4.07/1.69  #Split   : 1
% 4.07/1.69  #Chain   : 0
% 4.07/1.69  #Close   : 0
% 4.07/1.69  
% 4.07/1.69  Ordering : KBO
% 4.07/1.69  
% 4.07/1.69  Simplification rules
% 4.07/1.69  ----------------------
% 4.07/1.69  #Subsume      : 141
% 4.07/1.69  #Demod        : 130
% 4.07/1.69  #Tautology    : 120
% 4.07/1.69  #SimpNegUnit  : 62
% 4.07/1.69  #BackRed      : 1
% 4.07/1.69  
% 4.07/1.69  #Partial instantiations: 0
% 4.07/1.69  #Strategies tried      : 1
% 4.07/1.69  
% 4.07/1.69  Timing (in seconds)
% 4.07/1.69  ----------------------
% 4.07/1.70  Preprocessing        : 0.31
% 4.07/1.70  Parsing              : 0.16
% 4.07/1.70  CNF conversion       : 0.02
% 4.07/1.70  Main loop            : 0.63
% 4.07/1.70  Inferencing          : 0.21
% 4.07/1.70  Reduction            : 0.20
% 4.07/1.70  Demodulation         : 0.13
% 4.07/1.70  BG Simplification    : 0.02
% 4.07/1.70  Subsumption          : 0.15
% 4.07/1.70  Abstraction          : 0.03
% 4.07/1.70  MUC search           : 0.00
% 4.07/1.70  Cooper               : 0.00
% 4.07/1.70  Total                : 0.97
% 4.07/1.70  Index Insertion      : 0.00
% 4.07/1.70  Index Deletion       : 0.00
% 4.07/1.70  Index Matching       : 0.00
% 4.07/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
