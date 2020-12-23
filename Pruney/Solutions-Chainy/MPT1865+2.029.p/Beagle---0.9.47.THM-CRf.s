%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:21 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   52 (  78 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 250 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

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

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v2_tex_2(B,A)
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ~ ( r2_hidden(C,B)
                      & ! [D] :
                          ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v4_pre_topc(D,A)
                              & k9_subset_1(u1_struct_0(A),B,D) = k1_tarski(C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_65,axiom,(
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

tff(c_28,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_79,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(k2_tarski(A_65,B_66),C_67)
      | ~ r2_hidden(B_66,C_67)
      | ~ r2_hidden(A_65,C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_88,plain,(
    ! [A_1,C_67] :
      ( r1_tarski(k1_tarski(A_1),C_67)
      | ~ r2_hidden(A_1,C_67)
      | ~ r2_hidden(A_1,C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_66,plain,(
    ! [C_60,A_61,B_62] :
      ( r2_hidden(C_60,A_61)
      | ~ r2_hidden(C_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_70,plain,(
    ! [A_63] :
      ( r2_hidden('#skF_5',A_63)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_74,plain,(
    r2_hidden('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_70])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k1_tarski(A_9),k1_zfmisc_1(B_10))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_138,plain,(
    ! [A_78,B_79,C_80] :
      ( v4_pre_topc('#skF_1'(A_78,B_79,C_80),A_78)
      | ~ r1_tarski(C_80,B_79)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_147,plain,(
    ! [A_78,B_79,A_9] :
      ( v4_pre_topc('#skF_1'(A_78,B_79,k1_tarski(A_9)),A_78)
      | ~ r1_tarski(k1_tarski(A_9),B_79)
      | ~ v2_tex_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ r2_hidden(A_9,u1_struct_0(A_78)) ) ),
    inference(resolution,[status(thm)],[c_12,c_138])).

tff(c_205,plain,(
    ! [A_97,B_98,C_99] :
      ( k9_subset_1(u1_struct_0(A_97),B_98,'#skF_1'(A_97,B_98,C_99)) = C_99
      | ~ r1_tarski(C_99,B_98)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ v2_tex_2(B_98,A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_270,plain,(
    ! [A_104,B_105,A_106] :
      ( k9_subset_1(u1_struct_0(A_104),B_105,'#skF_1'(A_104,B_105,k1_tarski(A_106))) = k1_tarski(A_106)
      | ~ r1_tarski(k1_tarski(A_106),B_105)
      | ~ v2_tex_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104)
      | ~ r2_hidden(A_106,u1_struct_0(A_104)) ) ),
    inference(resolution,[status(thm)],[c_12,c_205])).

tff(c_151,plain,(
    ! [A_81,B_82,C_83] :
      ( m1_subset_1('#skF_1'(A_81,B_82,C_83),k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ r1_tarski(C_83,B_82)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ v2_tex_2(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [D_47] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',D_47) != k1_tarski('#skF_5')
      | ~ v4_pre_topc(D_47,'#skF_3')
      | ~ m1_subset_1(D_47,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_163,plain,(
    ! [B_82,C_83] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_82,C_83)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_82,C_83),'#skF_3')
      | ~ r1_tarski(C_83,B_82)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_151,c_26])).

tff(c_171,plain,(
    ! [B_82,C_83] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4','#skF_1'('#skF_3',B_82,C_83)) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3',B_82,C_83),'#skF_3')
      | ~ r1_tarski(C_83,B_82)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2(B_82,'#skF_3')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_163])).

tff(c_278,plain,(
    ! [A_106] :
      ( k1_tarski(A_106) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_106)),'#skF_3')
      | ~ r1_tarski(k1_tarski(A_106),'#skF_4')
      | ~ m1_subset_1(k1_tarski(A_106),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k1_tarski(A_106),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_106,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_171])).

tff(c_286,plain,(
    ! [A_107] :
      ( k1_tarski(A_107) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_107)),'#skF_3')
      | ~ m1_subset_1(k1_tarski(A_107),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(k1_tarski(A_107),'#skF_4')
      | ~ r2_hidden(A_107,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_34,c_32,c_278])).

tff(c_292,plain,(
    ! [A_108] :
      ( k1_tarski(A_108) != k1_tarski('#skF_5')
      | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4',k1_tarski(A_108)),'#skF_3')
      | ~ r1_tarski(k1_tarski(A_108),'#skF_4')
      | ~ r2_hidden(A_108,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12,c_286])).

tff(c_296,plain,(
    ! [A_9] :
      ( k1_tarski(A_9) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_9),'#skF_4')
      | ~ v2_tex_2('#skF_4','#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_9,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_147,c_292])).

tff(c_300,plain,(
    ! [A_109] :
      ( k1_tarski(A_109) != k1_tarski('#skF_5')
      | ~ r1_tarski(k1_tarski(A_109),'#skF_4')
      | ~ r2_hidden(A_109,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_296])).

tff(c_304,plain,(
    ~ r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_300])).

tff(c_307,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_304])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:51:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.29  
% 2.28/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.30  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.28/1.30  
% 2.28/1.30  %Foreground sorts:
% 2.28/1.30  
% 2.28/1.30  
% 2.28/1.30  %Background operators:
% 2.28/1.30  
% 2.28/1.30  
% 2.28/1.30  %Foreground operators:
% 2.28/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.28/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.30  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.28/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.28/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.28/1.30  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.28/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.30  
% 2.28/1.31  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 2.28/1.31  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.28/1.31  tff(f_33, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.28/1.31  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.28/1.31  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.28/1.31  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 2.28/1.31  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.28/1.31  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.31  tff(c_79, plain, (![A_65, B_66, C_67]: (r1_tarski(k2_tarski(A_65, B_66), C_67) | ~r2_hidden(B_66, C_67) | ~r2_hidden(A_65, C_67))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.31  tff(c_88, plain, (![A_1, C_67]: (r1_tarski(k1_tarski(A_1), C_67) | ~r2_hidden(A_1, C_67) | ~r2_hidden(A_1, C_67))), inference(superposition, [status(thm), theory('equality')], [c_2, c_79])).
% 2.28/1.31  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.28/1.31  tff(c_66, plain, (![C_60, A_61, B_62]: (r2_hidden(C_60, A_61) | ~r2_hidden(C_60, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.28/1.31  tff(c_70, plain, (![A_63]: (r2_hidden('#skF_5', A_63) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_28, c_66])).
% 2.28/1.31  tff(c_74, plain, (r2_hidden('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_70])).
% 2.28/1.31  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.28/1.31  tff(c_32, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.28/1.31  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(k1_tarski(A_9), k1_zfmisc_1(B_10)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.28/1.31  tff(c_138, plain, (![A_78, B_79, C_80]: (v4_pre_topc('#skF_1'(A_78, B_79, C_80), A_78) | ~r1_tarski(C_80, B_79) | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_78))) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.28/1.31  tff(c_147, plain, (![A_78, B_79, A_9]: (v4_pre_topc('#skF_1'(A_78, B_79, k1_tarski(A_9)), A_78) | ~r1_tarski(k1_tarski(A_9), B_79) | ~v2_tex_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_78))) | ~l1_pre_topc(A_78) | ~r2_hidden(A_9, u1_struct_0(A_78)))), inference(resolution, [status(thm)], [c_12, c_138])).
% 2.28/1.31  tff(c_205, plain, (![A_97, B_98, C_99]: (k9_subset_1(u1_struct_0(A_97), B_98, '#skF_1'(A_97, B_98, C_99))=C_99 | ~r1_tarski(C_99, B_98) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_97))) | ~v2_tex_2(B_98, A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.28/1.31  tff(c_270, plain, (![A_104, B_105, A_106]: (k9_subset_1(u1_struct_0(A_104), B_105, '#skF_1'(A_104, B_105, k1_tarski(A_106)))=k1_tarski(A_106) | ~r1_tarski(k1_tarski(A_106), B_105) | ~v2_tex_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104) | ~r2_hidden(A_106, u1_struct_0(A_104)))), inference(resolution, [status(thm)], [c_12, c_205])).
% 2.28/1.31  tff(c_151, plain, (![A_81, B_82, C_83]: (m1_subset_1('#skF_1'(A_81, B_82, C_83), k1_zfmisc_1(u1_struct_0(A_81))) | ~r1_tarski(C_83, B_82) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(A_81))) | ~v2_tex_2(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.28/1.31  tff(c_26, plain, (![D_47]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', D_47)!=k1_tarski('#skF_5') | ~v4_pre_topc(D_47, '#skF_3') | ~m1_subset_1(D_47, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.28/1.31  tff(c_163, plain, (![B_82, C_83]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_82, C_83))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_82, C_83), '#skF_3') | ~r1_tarski(C_83, B_82) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_82, '#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_151, c_26])).
% 2.28/1.31  tff(c_171, plain, (![B_82, C_83]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', '#skF_1'('#skF_3', B_82, C_83))!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', B_82, C_83), '#skF_3') | ~r1_tarski(C_83, B_82) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2(B_82, '#skF_3') | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_163])).
% 2.28/1.31  tff(c_278, plain, (![A_106]: (k1_tarski(A_106)!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_106)), '#skF_3') | ~r1_tarski(k1_tarski(A_106), '#skF_4') | ~m1_subset_1(k1_tarski(A_106), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k1_tarski(A_106), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_106, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_270, c_171])).
% 2.28/1.31  tff(c_286, plain, (![A_107]: (k1_tarski(A_107)!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_107)), '#skF_3') | ~m1_subset_1(k1_tarski(A_107), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(k1_tarski(A_107), '#skF_4') | ~r2_hidden(A_107, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_34, c_32, c_278])).
% 2.28/1.31  tff(c_292, plain, (![A_108]: (k1_tarski(A_108)!=k1_tarski('#skF_5') | ~v4_pre_topc('#skF_1'('#skF_3', '#skF_4', k1_tarski(A_108)), '#skF_3') | ~r1_tarski(k1_tarski(A_108), '#skF_4') | ~r2_hidden(A_108, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12, c_286])).
% 2.28/1.31  tff(c_296, plain, (![A_9]: (k1_tarski(A_9)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_9), '#skF_4') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_9, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_147, c_292])).
% 2.28/1.31  tff(c_300, plain, (![A_109]: (k1_tarski(A_109)!=k1_tarski('#skF_5') | ~r1_tarski(k1_tarski(A_109), '#skF_4') | ~r2_hidden(A_109, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_296])).
% 2.28/1.31  tff(c_304, plain, (~r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_74, c_300])).
% 2.28/1.31  tff(c_307, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_88, c_304])).
% 2.28/1.31  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_307])).
% 2.28/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.31  
% 2.28/1.31  Inference rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Ref     : 0
% 2.28/1.31  #Sup     : 53
% 2.28/1.31  #Fact    : 0
% 2.28/1.31  #Define  : 0
% 2.28/1.31  #Split   : 2
% 2.28/1.31  #Chain   : 0
% 2.28/1.31  #Close   : 0
% 2.28/1.31  
% 2.28/1.31  Ordering : KBO
% 2.28/1.31  
% 2.28/1.31  Simplification rules
% 2.28/1.31  ----------------------
% 2.28/1.31  #Subsume      : 4
% 2.28/1.31  #Demod        : 26
% 2.28/1.31  #Tautology    : 16
% 2.28/1.31  #SimpNegUnit  : 0
% 2.28/1.31  #BackRed      : 0
% 2.28/1.31  
% 2.28/1.31  #Partial instantiations: 0
% 2.28/1.31  #Strategies tried      : 1
% 2.28/1.31  
% 2.28/1.31  Timing (in seconds)
% 2.28/1.31  ----------------------
% 2.28/1.31  Preprocessing        : 0.31
% 2.28/1.31  Parsing              : 0.16
% 2.28/1.31  CNF conversion       : 0.02
% 2.28/1.31  Main loop            : 0.24
% 2.28/1.31  Inferencing          : 0.10
% 2.28/1.31  Reduction            : 0.06
% 2.28/1.31  Demodulation         : 0.05
% 2.28/1.31  BG Simplification    : 0.02
% 2.28/1.31  Subsumption          : 0.05
% 2.28/1.31  Abstraction          : 0.01
% 2.28/1.31  MUC search           : 0.00
% 2.28/1.31  Cooper               : 0.00
% 2.28/1.31  Total                : 0.58
% 2.28/1.31  Index Insertion      : 0.00
% 2.28/1.31  Index Deletion       : 0.00
% 2.28/1.31  Index Matching       : 0.00
% 2.28/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
