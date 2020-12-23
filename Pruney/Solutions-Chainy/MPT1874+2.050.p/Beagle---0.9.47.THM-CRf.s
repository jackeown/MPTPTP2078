%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:43 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 100 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 258 expanded)
%              Number of equality atoms :   10 (  28 expanded)
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

tff(f_98,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_78,axiom,(
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

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k1_tarski(A_11),k1_zfmisc_1(B_12))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_139,plain,(
    ! [C_60,A_61,B_62] :
      ( r2_hidden(C_60,A_61)
      | ~ r2_hidden(C_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_225,plain,(
    ! [A_80,B_81,A_82] :
      ( r2_hidden('#skF_1'(A_80,B_81),A_82)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(A_82))
      | r1_tarski(A_80,B_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_139])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_247,plain,(
    ! [A_83,A_84] :
      ( ~ m1_subset_1(A_83,k1_zfmisc_1(A_84))
      | r1_tarski(A_83,A_84) ) ),
    inference(resolution,[status(thm)],[c_225,c_4])).

tff(c_254,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k1_tarski(A_11),B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_12,c_247])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_149,plain,(
    ! [A_63] :
      ( r2_hidden('#skF_5',A_63)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_28,c_139])).

tff(c_153,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_149])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_515,plain,(
    ! [A_141,B_142,C_143] :
      ( k9_subset_1(u1_struct_0(A_141),B_142,k2_pre_topc(A_141,C_143)) = C_143
      | ~ r1_tarski(C_143,B_142)
      | ~ m1_subset_1(C_143,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ v2_tex_2(B_142,A_141)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1267,plain,(
    ! [A_239,B_240,A_241] :
      ( k9_subset_1(u1_struct_0(A_239),B_240,k2_pre_topc(A_239,k1_tarski(A_241))) = k1_tarski(A_241)
      | ~ r1_tarski(k1_tarski(A_241),B_240)
      | ~ v2_tex_2(B_240,A_239)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239)
      | ~ r2_hidden(A_241,u1_struct_0(A_239)) ) ),
    inference(resolution,[status(thm)],[c_12,c_515])).

tff(c_59,plain,(
    ! [C_40,B_41,A_42] :
      ( ~ v1_xboole_0(C_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(C_40))
      | ~ r2_hidden(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_65,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_42,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_66,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_113,plain,(
    ! [A_57,B_58] :
      ( k6_domain_1(A_57,B_58) = k1_tarski(B_58)
      | ~ m1_subset_1(B_58,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_122,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_127,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_122])).

tff(c_26,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_134,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_127,c_26])).

tff(c_1273,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1267,c_134])).

tff(c_1280,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_38,c_36,c_34,c_32,c_1273])).

tff(c_1281,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1280])).

tff(c_1285,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_254,c_1281])).

tff(c_1289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1285])).

tff(c_1290,plain,(
    ! [A_42] : ~ r2_hidden(A_42,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_1293,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1290,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:45:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.75  
% 4.37/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.76  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.37/1.76  
% 4.37/1.76  %Foreground sorts:
% 4.37/1.76  
% 4.37/1.76  
% 4.37/1.76  %Background operators:
% 4.37/1.76  
% 4.37/1.76  
% 4.37/1.76  %Foreground operators:
% 4.37/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.37/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.37/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.37/1.76  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.37/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.37/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.37/1.76  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.37/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.37/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.37/1.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.37/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.37/1.76  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.37/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.37/1.76  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.37/1.76  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.37/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.76  
% 4.42/1.77  tff(f_98, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 4.42/1.77  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 4.42/1.77  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.42/1.77  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.42/1.77  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 4.42/1.77  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.42/1.77  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.42/1.77  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/1.77  tff(c_12, plain, (![A_11, B_12]: (m1_subset_1(k1_tarski(A_11), k1_zfmisc_1(B_12)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.42/1.77  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.42/1.77  tff(c_139, plain, (![C_60, A_61, B_62]: (r2_hidden(C_60, A_61) | ~r2_hidden(C_60, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.42/1.77  tff(c_225, plain, (![A_80, B_81, A_82]: (r2_hidden('#skF_1'(A_80, B_81), A_82) | ~m1_subset_1(A_80, k1_zfmisc_1(A_82)) | r1_tarski(A_80, B_81))), inference(resolution, [status(thm)], [c_6, c_139])).
% 4.42/1.77  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.42/1.77  tff(c_247, plain, (![A_83, A_84]: (~m1_subset_1(A_83, k1_zfmisc_1(A_84)) | r1_tarski(A_83, A_84))), inference(resolution, [status(thm)], [c_225, c_4])).
% 4.42/1.77  tff(c_254, plain, (![A_11, B_12]: (r1_tarski(k1_tarski(A_11), B_12) | ~r2_hidden(A_11, B_12))), inference(resolution, [status(thm)], [c_12, c_247])).
% 4.42/1.77  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/1.77  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/1.77  tff(c_149, plain, (![A_63]: (r2_hidden('#skF_5', A_63) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_28, c_139])).
% 4.42/1.77  tff(c_153, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_149])).
% 4.42/1.77  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/1.77  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/1.77  tff(c_32, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/1.77  tff(c_515, plain, (![A_141, B_142, C_143]: (k9_subset_1(u1_struct_0(A_141), B_142, k2_pre_topc(A_141, C_143))=C_143 | ~r1_tarski(C_143, B_142) | ~m1_subset_1(C_143, k1_zfmisc_1(u1_struct_0(A_141))) | ~v2_tex_2(B_142, A_141) | ~m1_subset_1(B_142, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.42/1.77  tff(c_1267, plain, (![A_239, B_240, A_241]: (k9_subset_1(u1_struct_0(A_239), B_240, k2_pre_topc(A_239, k1_tarski(A_241)))=k1_tarski(A_241) | ~r1_tarski(k1_tarski(A_241), B_240) | ~v2_tex_2(B_240, A_239) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239) | v2_struct_0(A_239) | ~r2_hidden(A_241, u1_struct_0(A_239)))), inference(resolution, [status(thm)], [c_12, c_515])).
% 4.42/1.77  tff(c_59, plain, (![C_40, B_41, A_42]: (~v1_xboole_0(C_40) | ~m1_subset_1(B_41, k1_zfmisc_1(C_40)) | ~r2_hidden(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.42/1.77  tff(c_65, plain, (![A_42]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_42, '#skF_4'))), inference(resolution, [status(thm)], [c_34, c_59])).
% 4.42/1.77  tff(c_66, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_65])).
% 4.42/1.77  tff(c_30, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/1.77  tff(c_113, plain, (![A_57, B_58]: (k6_domain_1(A_57, B_58)=k1_tarski(B_58) | ~m1_subset_1(B_58, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.42/1.77  tff(c_122, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_113])).
% 4.42/1.77  tff(c_127, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_122])).
% 4.42/1.77  tff(c_26, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/1.77  tff(c_134, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_127, c_26])).
% 4.42/1.77  tff(c_1273, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1267, c_134])).
% 4.42/1.77  tff(c_1280, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_38, c_36, c_34, c_32, c_1273])).
% 4.42/1.77  tff(c_1281, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_1280])).
% 4.42/1.77  tff(c_1285, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_254, c_1281])).
% 4.42/1.77  tff(c_1289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1285])).
% 4.42/1.77  tff(c_1290, plain, (![A_42]: (~r2_hidden(A_42, '#skF_4'))), inference(splitRight, [status(thm)], [c_65])).
% 4.42/1.77  tff(c_1293, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1290, c_28])).
% 4.42/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.77  
% 4.42/1.77  Inference rules
% 4.42/1.77  ----------------------
% 4.42/1.77  #Ref     : 0
% 4.42/1.77  #Sup     : 329
% 4.42/1.77  #Fact    : 0
% 4.42/1.77  #Define  : 0
% 4.42/1.77  #Split   : 8
% 4.42/1.77  #Chain   : 0
% 4.42/1.77  #Close   : 0
% 4.42/1.77  
% 4.42/1.77  Ordering : KBO
% 4.42/1.77  
% 4.42/1.77  Simplification rules
% 4.42/1.77  ----------------------
% 4.42/1.77  #Subsume      : 107
% 4.42/1.77  #Demod        : 38
% 4.42/1.77  #Tautology    : 30
% 4.42/1.77  #SimpNegUnit  : 7
% 4.42/1.77  #BackRed      : 2
% 4.42/1.77  
% 4.42/1.77  #Partial instantiations: 0
% 4.42/1.77  #Strategies tried      : 1
% 4.42/1.77  
% 4.42/1.77  Timing (in seconds)
% 4.42/1.77  ----------------------
% 4.42/1.78  Preprocessing        : 0.33
% 4.42/1.78  Parsing              : 0.17
% 4.42/1.78  CNF conversion       : 0.03
% 4.42/1.78  Main loop            : 0.67
% 4.42/1.78  Inferencing          : 0.22
% 4.42/1.78  Reduction            : 0.18
% 4.42/1.78  Demodulation         : 0.11
% 4.42/1.78  BG Simplification    : 0.02
% 4.42/1.78  Subsumption          : 0.20
% 4.42/1.78  Abstraction          : 0.03
% 4.42/1.78  MUC search           : 0.00
% 4.42/1.78  Cooper               : 0.00
% 4.42/1.78  Total                : 1.04
% 4.42/1.78  Index Insertion      : 0.00
% 4.42/1.78  Index Deletion       : 0.00
% 4.42/1.78  Index Matching       : 0.00
% 4.42/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
