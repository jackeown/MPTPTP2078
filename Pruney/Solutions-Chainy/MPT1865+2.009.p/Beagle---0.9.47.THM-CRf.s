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
% DateTime   : Thu Dec  3 10:29:18 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   59 (  91 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 ( 286 expanded)
%              Number of equality atoms :   15 (  31 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_77,axiom,(
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

tff(c_34,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_93,plain,(
    ! [C_69,B_70,A_71] :
      ( ~ v1_xboole_0(C_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(C_69))
      | ~ r2_hidden(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_99,plain,(
    ! [A_71] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_71,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_93])).

tff(c_100,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k1_tarski(A_10),k1_zfmisc_1(B_11))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_137,plain,(
    ! [A_82,B_83,C_84] :
      ( v4_pre_topc('#skF_2'(A_82,B_83,C_84),A_82)
      | ~ r1_tarski(C_84,B_83)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ v2_tex_2(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_146,plain,(
    ! [A_82,B_83,A_10] :
      ( v4_pre_topc('#skF_2'(A_82,B_83,k1_tarski(A_10)),A_82)
      | ~ r1_tarski(k1_tarski(A_10),B_83)
      | ~ v2_tex_2(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82)
      | ~ r2_hidden(A_10,u1_struct_0(A_82)) ) ),
    inference(resolution,[status(thm)],[c_14,c_137])).

tff(c_262,plain,(
    ! [A_107,B_108,C_109] :
      ( k9_subset_1(u1_struct_0(A_107),B_108,'#skF_2'(A_107,B_108,C_109)) = C_109
      | ~ r1_tarski(C_109,B_108)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ v2_tex_2(B_108,A_107)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_322,plain,(
    ! [A_116,B_117,A_118] :
      ( k9_subset_1(u1_struct_0(A_116),B_117,'#skF_2'(A_116,B_117,k1_tarski(A_118))) = k1_tarski(A_118)
      | ~ r1_tarski(k1_tarski(A_118),B_117)
      | ~ v2_tex_2(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ r2_hidden(A_118,u1_struct_0(A_116)) ) ),
    inference(resolution,[status(thm)],[c_14,c_262])).

tff(c_222,plain,(
    ! [A_101,B_102,C_103] :
      ( m1_subset_1('#skF_2'(A_101,B_102,C_103),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ r1_tarski(C_103,B_102)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ v2_tex_2(B_102,A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [D_53] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5',D_53) != k1_tarski('#skF_6')
      | ~ v4_pre_topc(D_53,'#skF_4')
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_245,plain,(
    ! [B_102,C_103] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_102,C_103)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_2'('#skF_4',B_102,C_103),'#skF_4')
      | ~ r1_tarski(C_103,B_102)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_102,'#skF_4')
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_222,c_32])).

tff(c_259,plain,(
    ! [B_102,C_103] :
      ( k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_2'('#skF_4',B_102,C_103)) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_2'('#skF_4',B_102,C_103),'#skF_4')
      | ~ r1_tarski(C_103,B_102)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2(B_102,'#skF_4')
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_245])).

tff(c_328,plain,(
    ! [A_118] :
      ( k1_tarski(A_118) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',k1_tarski(A_118)),'#skF_4')
      | ~ r1_tarski(k1_tarski(A_118),'#skF_5')
      | ~ m1_subset_1(k1_tarski(A_118),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(k1_tarski(A_118),'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(A_118,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_259])).

tff(c_338,plain,(
    ! [A_119] :
      ( k1_tarski(A_119) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',k1_tarski(A_119)),'#skF_4')
      | ~ m1_subset_1(k1_tarski(A_119),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(k1_tarski(A_119),'#skF_5')
      | ~ r2_hidden(A_119,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_40,c_38,c_328])).

tff(c_344,plain,(
    ! [A_120] :
      ( k1_tarski(A_120) != k1_tarski('#skF_6')
      | ~ v4_pre_topc('#skF_2'('#skF_4','#skF_5',k1_tarski(A_120)),'#skF_4')
      | ~ r1_tarski(k1_tarski(A_120),'#skF_5')
      | ~ r2_hidden(A_120,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_14,c_338])).

tff(c_348,plain,(
    ! [A_10] :
      ( k1_tarski(A_10) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(A_10),'#skF_5')
      | ~ v2_tex_2('#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r2_hidden(A_10,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_146,c_344])).

tff(c_352,plain,(
    ! [A_121] :
      ( k1_tarski(A_121) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(A_121),'#skF_5')
      | ~ r2_hidden(A_121,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_348])).

tff(c_356,plain,(
    ! [A_12] :
      ( k1_tarski(A_12) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(A_12),'#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_12,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16,c_352])).

tff(c_367,plain,(
    ! [A_122] :
      ( k1_tarski(A_122) != k1_tarski('#skF_6')
      | ~ r1_tarski(k1_tarski(A_122),'#skF_5')
      | ~ m1_subset_1(A_122,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_356])).

tff(c_373,plain,(
    ! [A_123] :
      ( k1_tarski(A_123) != k1_tarski('#skF_6')
      | ~ m1_subset_1(A_123,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_123,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_12,c_367])).

tff(c_376,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_373])).

tff(c_380,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_376])).

tff(c_381,plain,(
    ! [A_71] : ~ r2_hidden(A_71,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_34])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  
% 2.75/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.39  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 2.75/1.39  
% 2.75/1.39  %Foreground sorts:
% 2.75/1.39  
% 2.75/1.39  
% 2.75/1.39  %Background operators:
% 2.75/1.39  
% 2.75/1.39  
% 2.75/1.39  %Foreground operators:
% 2.75/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.75/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.75/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.75/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.75/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.75/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.75/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.39  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.75/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.75/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.75/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.75/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.39  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.75/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.39  
% 2.75/1.40  tff(f_99, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k1_tarski(C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tex_2)).
% 2.75/1.40  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.75/1.40  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.75/1.40  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.75/1.40  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.75/1.40  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 2.75/1.40  tff(c_34, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.75/1.40  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.75/1.40  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.40  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.75/1.40  tff(c_93, plain, (![C_69, B_70, A_71]: (~v1_xboole_0(C_69) | ~m1_subset_1(B_70, k1_zfmisc_1(C_69)) | ~r2_hidden(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.75/1.40  tff(c_99, plain, (![A_71]: (~v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden(A_71, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_93])).
% 2.75/1.40  tff(c_100, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_99])).
% 2.75/1.40  tff(c_16, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.75/1.40  tff(c_42, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.75/1.40  tff(c_38, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.75/1.40  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(k1_tarski(A_10), k1_zfmisc_1(B_11)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.75/1.40  tff(c_137, plain, (![A_82, B_83, C_84]: (v4_pre_topc('#skF_2'(A_82, B_83, C_84), A_82) | ~r1_tarski(C_84, B_83) | ~m1_subset_1(C_84, k1_zfmisc_1(u1_struct_0(A_82))) | ~v2_tex_2(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.75/1.40  tff(c_146, plain, (![A_82, B_83, A_10]: (v4_pre_topc('#skF_2'(A_82, B_83, k1_tarski(A_10)), A_82) | ~r1_tarski(k1_tarski(A_10), B_83) | ~v2_tex_2(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82) | ~r2_hidden(A_10, u1_struct_0(A_82)))), inference(resolution, [status(thm)], [c_14, c_137])).
% 2.75/1.40  tff(c_262, plain, (![A_107, B_108, C_109]: (k9_subset_1(u1_struct_0(A_107), B_108, '#skF_2'(A_107, B_108, C_109))=C_109 | ~r1_tarski(C_109, B_108) | ~m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(A_107))) | ~v2_tex_2(B_108, A_107) | ~m1_subset_1(B_108, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.75/1.40  tff(c_322, plain, (![A_116, B_117, A_118]: (k9_subset_1(u1_struct_0(A_116), B_117, '#skF_2'(A_116, B_117, k1_tarski(A_118)))=k1_tarski(A_118) | ~r1_tarski(k1_tarski(A_118), B_117) | ~v2_tex_2(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~r2_hidden(A_118, u1_struct_0(A_116)))), inference(resolution, [status(thm)], [c_14, c_262])).
% 2.75/1.40  tff(c_222, plain, (![A_101, B_102, C_103]: (m1_subset_1('#skF_2'(A_101, B_102, C_103), k1_zfmisc_1(u1_struct_0(A_101))) | ~r1_tarski(C_103, B_102) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0(A_101))) | ~v2_tex_2(B_102, A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.75/1.40  tff(c_32, plain, (![D_53]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', D_53)!=k1_tarski('#skF_6') | ~v4_pre_topc(D_53, '#skF_4') | ~m1_subset_1(D_53, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.75/1.40  tff(c_245, plain, (![B_102, C_103]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_102, C_103))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_4', B_102, C_103), '#skF_4') | ~r1_tarski(C_103, B_102) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_102, '#skF_4') | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_222, c_32])).
% 2.75/1.40  tff(c_259, plain, (![B_102, C_103]: (k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_2'('#skF_4', B_102, C_103))!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_4', B_102, C_103), '#skF_4') | ~r1_tarski(C_103, B_102) | ~m1_subset_1(C_103, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2(B_102, '#skF_4') | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_245])).
% 2.75/1.40  tff(c_328, plain, (![A_118]: (k1_tarski(A_118)!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', k1_tarski(A_118)), '#skF_4') | ~r1_tarski(k1_tarski(A_118), '#skF_5') | ~m1_subset_1(k1_tarski(A_118), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(k1_tarski(A_118), '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r2_hidden(A_118, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_322, c_259])).
% 2.75/1.40  tff(c_338, plain, (![A_119]: (k1_tarski(A_119)!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', k1_tarski(A_119)), '#skF_4') | ~m1_subset_1(k1_tarski(A_119), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(k1_tarski(A_119), '#skF_5') | ~r2_hidden(A_119, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_40, c_38, c_328])).
% 2.75/1.40  tff(c_344, plain, (![A_120]: (k1_tarski(A_120)!=k1_tarski('#skF_6') | ~v4_pre_topc('#skF_2'('#skF_4', '#skF_5', k1_tarski(A_120)), '#skF_4') | ~r1_tarski(k1_tarski(A_120), '#skF_5') | ~r2_hidden(A_120, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_14, c_338])).
% 2.75/1.40  tff(c_348, plain, (![A_10]: (k1_tarski(A_10)!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(A_10), '#skF_5') | ~v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r2_hidden(A_10, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_146, c_344])).
% 2.75/1.40  tff(c_352, plain, (![A_121]: (k1_tarski(A_121)!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(A_121), '#skF_5') | ~r2_hidden(A_121, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_348])).
% 2.75/1.40  tff(c_356, plain, (![A_12]: (k1_tarski(A_12)!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(A_12), '#skF_5') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_12, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_16, c_352])).
% 2.75/1.40  tff(c_367, plain, (![A_122]: (k1_tarski(A_122)!=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski(A_122), '#skF_5') | ~m1_subset_1(A_122, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_100, c_356])).
% 2.75/1.40  tff(c_373, plain, (![A_123]: (k1_tarski(A_123)!=k1_tarski('#skF_6') | ~m1_subset_1(A_123, u1_struct_0('#skF_4')) | ~r2_hidden(A_123, '#skF_5'))), inference(resolution, [status(thm)], [c_12, c_367])).
% 2.75/1.40  tff(c_376, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_373])).
% 2.75/1.40  tff(c_380, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_376])).
% 2.75/1.40  tff(c_381, plain, (![A_71]: (~r2_hidden(A_71, '#skF_5'))), inference(splitRight, [status(thm)], [c_99])).
% 2.75/1.40  tff(c_384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_34])).
% 2.75/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.40  
% 2.75/1.40  Inference rules
% 2.75/1.40  ----------------------
% 2.75/1.40  #Ref     : 0
% 2.75/1.40  #Sup     : 65
% 2.75/1.40  #Fact    : 0
% 2.75/1.40  #Define  : 0
% 2.75/1.40  #Split   : 3
% 2.75/1.40  #Chain   : 0
% 2.75/1.40  #Close   : 0
% 2.75/1.40  
% 2.75/1.40  Ordering : KBO
% 2.75/1.40  
% 2.75/1.40  Simplification rules
% 2.75/1.40  ----------------------
% 2.75/1.40  #Subsume      : 9
% 2.75/1.40  #Demod        : 29
% 2.75/1.40  #Tautology    : 15
% 2.75/1.40  #SimpNegUnit  : 3
% 2.75/1.40  #BackRed      : 1
% 2.75/1.40  
% 2.75/1.40  #Partial instantiations: 0
% 2.75/1.40  #Strategies tried      : 1
% 2.75/1.40  
% 2.75/1.40  Timing (in seconds)
% 2.75/1.40  ----------------------
% 2.75/1.41  Preprocessing        : 0.33
% 2.75/1.41  Parsing              : 0.17
% 2.75/1.41  CNF conversion       : 0.03
% 2.75/1.41  Main loop            : 0.30
% 2.75/1.41  Inferencing          : 0.12
% 2.75/1.41  Reduction            : 0.08
% 2.75/1.41  Demodulation         : 0.06
% 2.75/1.41  BG Simplification    : 0.02
% 2.75/1.41  Subsumption          : 0.07
% 2.75/1.41  Abstraction          : 0.02
% 2.75/1.41  MUC search           : 0.00
% 2.75/1.41  Cooper               : 0.00
% 2.75/1.41  Total                : 0.67
% 2.75/1.41  Index Insertion      : 0.00
% 2.75/1.41  Index Deletion       : 0.00
% 2.75/1.41  Index Matching       : 0.00
% 2.75/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
