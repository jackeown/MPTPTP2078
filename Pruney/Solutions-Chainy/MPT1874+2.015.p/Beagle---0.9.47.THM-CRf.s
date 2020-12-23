%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:39 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 165 expanded)
%              Number of leaves         :   33 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 467 expanded)
%              Number of equality atoms :   15 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_84,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_179,plain,(
    ! [A_70,B_71,C_72] :
      ( r1_tarski(k2_tarski(A_70,B_71),C_72)
      | ~ r2_hidden(B_71,C_72)
      | ~ r2_hidden(A_70,C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_201,plain,(
    ! [A_8,C_72] :
      ( r1_tarski(k1_tarski(A_8),C_72)
      | ~ r2_hidden(A_8,C_72)
      | ~ r2_hidden(A_8,C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_179])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_69,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_77,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_113,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,C_58)
      | ~ r1_tarski(B_59,C_58)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [A_57] :
      ( r1_tarski(A_57,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_77,c_113])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_671,plain,(
    ! [A_132,B_133,C_134] :
      ( k9_subset_1(u1_struct_0(A_132),B_133,k2_pre_topc(A_132,C_134)) = C_134
      | ~ r1_tarski(C_134,B_133)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ v2_tex_2(B_133,A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1621,plain,(
    ! [A_219,B_220,A_221] :
      ( k9_subset_1(u1_struct_0(A_219),B_220,k2_pre_topc(A_219,A_221)) = A_221
      | ~ r1_tarski(A_221,B_220)
      | ~ v2_tex_2(B_220,A_219)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219)
      | ~ r1_tarski(A_221,u1_struct_0(A_219)) ) ),
    inference(resolution,[status(thm)],[c_22,c_671])).

tff(c_1628,plain,(
    ! [A_221] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_221)) = A_221
      | ~ r1_tarski(A_221,'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_221,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1621])).

tff(c_1633,plain,(
    ! [A_221] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_221)) = A_221
      | ~ r1_tarski(A_221,'#skF_4')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(A_221,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_1628])).

tff(c_1635,plain,(
    ! [A_222] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',A_222)) = A_222
      | ~ r1_tarski(A_222,'#skF_4')
      | ~ r1_tarski(A_222,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1633])).

tff(c_49,plain,(
    ! [B_35,A_36] :
      ( ~ r2_hidden(B_35,A_36)
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_82,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_88,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_92,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_88])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_145,plain,(
    ! [A_62,B_63] :
      ( k6_domain_1(A_62,B_63) = k1_tarski(B_63)
      | ~ m1_subset_1(B_63,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_154,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_145])).

tff(c_159,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_154])).

tff(c_34,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),'#skF_5'))) != k6_domain_1(u1_struct_0('#skF_3'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_160,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_5'))) != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_159,c_34])).

tff(c_1664,plain,
    ( ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1635,c_160])).

tff(c_1668,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1664])).

tff(c_1676,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_116,c_1668])).

tff(c_1680,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_201,c_1676])).

tff(c_1684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1680])).

tff(c_1685,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1664])).

tff(c_1689,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_201,c_1685])).

tff(c_1693,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:32:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.87  
% 4.68/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.87  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 4.68/1.87  
% 4.68/1.87  %Foreground sorts:
% 4.68/1.87  
% 4.68/1.87  
% 4.68/1.87  %Background operators:
% 4.68/1.87  
% 4.68/1.87  
% 4.68/1.87  %Foreground operators:
% 4.68/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.68/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.68/1.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.68/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.68/1.87  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.68/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.68/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.68/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.68/1.87  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 4.68/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.68/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.68/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.68/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.87  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.68/1.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.68/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.87  
% 4.68/1.88  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_tex_2)).
% 4.68/1.88  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.68/1.88  tff(f_47, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.68/1.88  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.68/1.88  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.68/1.88  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, C)) = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tex_2)).
% 4.68/1.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.68/1.88  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.68/1.88  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.68/1.88  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.68/1.88  tff(c_8, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.68/1.88  tff(c_179, plain, (![A_70, B_71, C_72]: (r1_tarski(k2_tarski(A_70, B_71), C_72) | ~r2_hidden(B_71, C_72) | ~r2_hidden(A_70, C_72))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.68/1.88  tff(c_201, plain, (![A_8, C_72]: (r1_tarski(k1_tarski(A_8), C_72) | ~r2_hidden(A_8, C_72) | ~r2_hidden(A_8, C_72))), inference(superposition, [status(thm), theory('equality')], [c_8, c_179])).
% 4.68/1.88  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.68/1.88  tff(c_69, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.68/1.88  tff(c_77, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_69])).
% 4.68/1.88  tff(c_113, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, C_58) | ~r1_tarski(B_59, C_58) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.88  tff(c_116, plain, (![A_57]: (r1_tarski(A_57, u1_struct_0('#skF_3')) | ~r1_tarski(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_77, c_113])).
% 4.68/1.88  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.68/1.88  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.68/1.88  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.68/1.88  tff(c_40, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.68/1.88  tff(c_22, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.68/1.88  tff(c_671, plain, (![A_132, B_133, C_134]: (k9_subset_1(u1_struct_0(A_132), B_133, k2_pre_topc(A_132, C_134))=C_134 | ~r1_tarski(C_134, B_133) | ~m1_subset_1(C_134, k1_zfmisc_1(u1_struct_0(A_132))) | ~v2_tex_2(B_133, A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132) | v2_struct_0(A_132))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.68/1.88  tff(c_1621, plain, (![A_219, B_220, A_221]: (k9_subset_1(u1_struct_0(A_219), B_220, k2_pre_topc(A_219, A_221))=A_221 | ~r1_tarski(A_221, B_220) | ~v2_tex_2(B_220, A_219) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219) | ~r1_tarski(A_221, u1_struct_0(A_219)))), inference(resolution, [status(thm)], [c_22, c_671])).
% 4.68/1.88  tff(c_1628, plain, (![A_221]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_221))=A_221 | ~r1_tarski(A_221, '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(A_221, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_42, c_1621])).
% 4.68/1.88  tff(c_1633, plain, (![A_221]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_221))=A_221 | ~r1_tarski(A_221, '#skF_4') | v2_struct_0('#skF_3') | ~r1_tarski(A_221, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_1628])).
% 4.68/1.88  tff(c_1635, plain, (![A_222]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', A_222))=A_222 | ~r1_tarski(A_222, '#skF_4') | ~r1_tarski(A_222, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_48, c_1633])).
% 4.68/1.88  tff(c_49, plain, (![B_35, A_36]: (~r2_hidden(B_35, A_36) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.68/1.88  tff(c_53, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_49])).
% 4.68/1.88  tff(c_82, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.68/1.88  tff(c_88, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_82])).
% 4.68/1.88  tff(c_92, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_53, c_88])).
% 4.68/1.88  tff(c_38, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.68/1.88  tff(c_145, plain, (![A_62, B_63]: (k6_domain_1(A_62, B_63)=k1_tarski(B_63) | ~m1_subset_1(B_63, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.68/1.88  tff(c_154, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_145])).
% 4.68/1.88  tff(c_159, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_154])).
% 4.68/1.88  tff(c_34, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')))!=k6_domain_1(u1_struct_0('#skF_3'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.68/1.88  tff(c_160, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_5')))!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_159, c_34])).
% 4.68/1.88  tff(c_1664, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4') | ~r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1635, c_160])).
% 4.68/1.88  tff(c_1668, plain, (~r1_tarski(k1_tarski('#skF_5'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1664])).
% 4.68/1.88  tff(c_1676, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_116, c_1668])).
% 4.68/1.88  tff(c_1680, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_201, c_1676])).
% 4.68/1.88  tff(c_1684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1680])).
% 4.68/1.88  tff(c_1685, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_1664])).
% 4.68/1.88  tff(c_1689, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_201, c_1685])).
% 4.68/1.88  tff(c_1693, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1689])).
% 4.68/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.88  
% 4.68/1.88  Inference rules
% 4.68/1.88  ----------------------
% 4.68/1.88  #Ref     : 0
% 4.68/1.88  #Sup     : 374
% 4.68/1.88  #Fact    : 0
% 4.68/1.88  #Define  : 0
% 4.68/1.88  #Split   : 7
% 4.68/1.88  #Chain   : 0
% 4.68/1.88  #Close   : 0
% 4.68/1.88  
% 4.68/1.88  Ordering : KBO
% 4.68/1.88  
% 4.68/1.88  Simplification rules
% 4.68/1.88  ----------------------
% 4.68/1.88  #Subsume      : 97
% 4.68/1.88  #Demod        : 82
% 4.68/1.88  #Tautology    : 40
% 4.68/1.88  #SimpNegUnit  : 35
% 4.68/1.88  #BackRed      : 2
% 4.68/1.88  
% 4.68/1.88  #Partial instantiations: 0
% 4.68/1.88  #Strategies tried      : 1
% 4.68/1.88  
% 4.68/1.88  Timing (in seconds)
% 4.68/1.88  ----------------------
% 4.68/1.89  Preprocessing        : 0.33
% 4.68/1.89  Parsing              : 0.18
% 4.68/1.89  CNF conversion       : 0.02
% 4.68/1.89  Main loop            : 0.76
% 4.68/1.89  Inferencing          : 0.23
% 4.68/1.89  Reduction            : 0.20
% 4.68/1.89  Demodulation         : 0.13
% 4.68/1.89  BG Simplification    : 0.03
% 4.68/1.89  Subsumption          : 0.25
% 4.68/1.89  Abstraction          : 0.03
% 4.68/1.89  MUC search           : 0.00
% 4.68/1.89  Cooper               : 0.00
% 4.68/1.89  Total                : 1.12
% 4.68/1.89  Index Insertion      : 0.00
% 4.68/1.89  Index Deletion       : 0.00
% 4.68/1.89  Index Matching       : 0.00
% 4.68/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
