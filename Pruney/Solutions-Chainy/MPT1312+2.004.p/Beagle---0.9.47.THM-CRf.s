%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:57 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :   67 (  78 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 119 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_40,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_67,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(A_44,k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_71,plain,(
    ~ r1_tarski('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_67,c_34])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_264,plain,(
    ! [A_79,C_80,B_81] :
      ( m1_subset_1(A_79,C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_271,plain,(
    ! [A_82] :
      ( m1_subset_1(A_82,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_82,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_264])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_278,plain,(
    ! [A_82] :
      ( r1_tarski(A_82,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_82,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_271,c_26])).

tff(c_12,plain,(
    ! [A_10] : k2_xboole_0(A_10,A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,(
    ! [A_12] : k3_tarski(k1_tarski(A_12)) = k2_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_81])).

tff(c_107,plain,(
    ! [A_52] : k3_tarski(k1_tarski(A_52)) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_93])).

tff(c_22,plain,(
    ! [A_17] : r1_tarski(A_17,k1_zfmisc_1(k3_tarski(A_17))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_119,plain,(
    ! [A_53] : r1_tarski(k1_tarski(A_53),k1_zfmisc_1(A_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_22])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | ~ r1_tarski(k1_tarski(A_13),B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_124,plain,(
    ! [A_54] : r2_hidden(A_54,k1_zfmisc_1(A_54)) ),
    inference(resolution,[status(thm)],[c_119,c_16])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_54] : ~ v1_xboole_0(k1_zfmisc_1(A_54)) ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_354,plain,(
    ! [C_90,A_91,B_92] :
      ( m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(B_92)))
      | ~ m1_pre_topc(B_92,A_91)
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_906,plain,(
    ! [A_148,A_149,B_150] :
      ( m1_subset_1(A_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_pre_topc(B_150,A_149)
      | ~ l1_pre_topc(A_149)
      | ~ r1_tarski(A_148,u1_struct_0(B_150)) ) ),
    inference(resolution,[status(thm)],[c_28,c_354])).

tff(c_908,plain,(
    ! [A_148] :
      ( m1_subset_1(A_148,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ r1_tarski(A_148,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_906])).

tff(c_941,plain,(
    ! [A_154] :
      ( m1_subset_1(A_154,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski(A_154,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_908])).

tff(c_132,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(A_58,B_59)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_140,plain,(
    ! [A_5,B_59] :
      ( r1_tarski(A_5,B_59)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1('#skF_2'(A_5,B_59),B_59) ) ),
    inference(resolution,[status(thm)],[c_132,c_8])).

tff(c_945,plain,(
    ! [A_5] :
      ( r1_tarski(A_5,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski('#skF_2'(A_5,k1_zfmisc_1(u1_struct_0('#skF_3'))),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_941,c_140])).

tff(c_10301,plain,(
    ! [A_567] :
      ( r1_tarski(A_567,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski('#skF_2'(A_567,k1_zfmisc_1(u1_struct_0('#skF_3'))),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_945])).

tff(c_10444,plain,(
    ! [A_568] :
      ( r1_tarski(A_568,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden('#skF_2'(A_568,k1_zfmisc_1(u1_struct_0('#skF_3'))),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_278,c_10301])).

tff(c_10452,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_10,c_10444])).

tff(c_10460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_71,c_10452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:31:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.67/3.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/3.07  
% 7.67/3.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/3.07  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v1_xboole_0 > l1_pre_topc > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 7.67/3.07  
% 7.67/3.07  %Foreground sorts:
% 7.67/3.07  
% 7.67/3.07  
% 7.67/3.07  %Background operators:
% 7.67/3.07  
% 7.67/3.07  
% 7.67/3.07  %Foreground operators:
% 7.67/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.67/3.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.67/3.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.67/3.07  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.67/3.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.67/3.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.67/3.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.67/3.07  tff('#skF_5', type, '#skF_5': $i).
% 7.67/3.07  tff('#skF_3', type, '#skF_3': $i).
% 7.67/3.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.67/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.67/3.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.67/3.07  tff('#skF_4', type, '#skF_4': $i).
% 7.67/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.67/3.07  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.67/3.07  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.67/3.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.67/3.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.67/3.07  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.67/3.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.67/3.07  
% 7.67/3.09  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.67/3.09  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 7.67/3.09  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.67/3.09  tff(f_66, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.67/3.09  tff(f_40, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.67/3.09  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 7.67/3.09  tff(f_48, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.67/3.09  tff(f_50, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 7.67/3.09  tff(f_46, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 7.67/3.09  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.67/3.09  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 7.67/3.09  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.67/3.09  tff(c_67, plain, (![A_44, B_45]: (m1_subset_1(A_44, k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.67/3.09  tff(c_34, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.67/3.09  tff(c_71, plain, (~r1_tarski('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_67, c_34])).
% 7.67/3.09  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.67/3.09  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.67/3.09  tff(c_264, plain, (![A_79, C_80, B_81]: (m1_subset_1(A_79, C_80) | ~m1_subset_1(B_81, k1_zfmisc_1(C_80)) | ~r2_hidden(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.67/3.09  tff(c_271, plain, (![A_82]: (m1_subset_1(A_82, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(A_82, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_264])).
% 7.67/3.09  tff(c_26, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.67/3.09  tff(c_278, plain, (![A_82]: (r1_tarski(A_82, u1_struct_0('#skF_4')) | ~r2_hidden(A_82, '#skF_5'))), inference(resolution, [status(thm)], [c_271, c_26])).
% 7.67/3.09  tff(c_12, plain, (![A_10]: (k2_xboole_0(A_10, A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.67/3.09  tff(c_14, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.67/3.09  tff(c_81, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.67/3.09  tff(c_93, plain, (![A_12]: (k3_tarski(k1_tarski(A_12))=k2_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_81])).
% 7.67/3.09  tff(c_107, plain, (![A_52]: (k3_tarski(k1_tarski(A_52))=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_93])).
% 7.67/3.09  tff(c_22, plain, (![A_17]: (r1_tarski(A_17, k1_zfmisc_1(k3_tarski(A_17))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.67/3.09  tff(c_119, plain, (![A_53]: (r1_tarski(k1_tarski(A_53), k1_zfmisc_1(A_53)))), inference(superposition, [status(thm), theory('equality')], [c_107, c_22])).
% 7.67/3.09  tff(c_16, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | ~r1_tarski(k1_tarski(A_13), B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.67/3.09  tff(c_124, plain, (![A_54]: (r2_hidden(A_54, k1_zfmisc_1(A_54)))), inference(resolution, [status(thm)], [c_119, c_16])).
% 7.67/3.09  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.67/3.09  tff(c_128, plain, (![A_54]: (~v1_xboole_0(k1_zfmisc_1(A_54)))), inference(resolution, [status(thm)], [c_124, c_2])).
% 7.67/3.09  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.67/3.09  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.67/3.09  tff(c_28, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.67/3.09  tff(c_354, plain, (![C_90, A_91, B_92]: (m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_91))) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(B_92))) | ~m1_pre_topc(B_92, A_91) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.67/3.09  tff(c_906, plain, (![A_148, A_149, B_150]: (m1_subset_1(A_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_pre_topc(B_150, A_149) | ~l1_pre_topc(A_149) | ~r1_tarski(A_148, u1_struct_0(B_150)))), inference(resolution, [status(thm)], [c_28, c_354])).
% 7.67/3.09  tff(c_908, plain, (![A_148]: (m1_subset_1(A_148, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~r1_tarski(A_148, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_38, c_906])).
% 7.67/3.09  tff(c_941, plain, (![A_154]: (m1_subset_1(A_154, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski(A_154, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_908])).
% 7.67/3.09  tff(c_132, plain, (![A_58, B_59]: (r2_hidden(A_58, B_59) | v1_xboole_0(B_59) | ~m1_subset_1(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.67/3.09  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.67/3.09  tff(c_140, plain, (![A_5, B_59]: (r1_tarski(A_5, B_59) | v1_xboole_0(B_59) | ~m1_subset_1('#skF_2'(A_5, B_59), B_59))), inference(resolution, [status(thm)], [c_132, c_8])).
% 7.67/3.09  tff(c_945, plain, (![A_5]: (r1_tarski(A_5, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_2'(A_5, k1_zfmisc_1(u1_struct_0('#skF_3'))), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_941, c_140])).
% 7.67/3.09  tff(c_10301, plain, (![A_567]: (r1_tarski(A_567, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_2'(A_567, k1_zfmisc_1(u1_struct_0('#skF_3'))), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_128, c_945])).
% 7.67/3.09  tff(c_10444, plain, (![A_568]: (r1_tarski(A_568, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_2'(A_568, k1_zfmisc_1(u1_struct_0('#skF_3'))), '#skF_5'))), inference(resolution, [status(thm)], [c_278, c_10301])).
% 7.67/3.09  tff(c_10452, plain, (r1_tarski('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_10, c_10444])).
% 7.67/3.09  tff(c_10460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_71, c_10452])).
% 7.67/3.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/3.09  
% 7.67/3.09  Inference rules
% 7.67/3.09  ----------------------
% 7.67/3.09  #Ref     : 0
% 7.67/3.09  #Sup     : 2355
% 7.67/3.09  #Fact    : 0
% 7.67/3.09  #Define  : 0
% 7.67/3.09  #Split   : 8
% 7.67/3.09  #Chain   : 0
% 7.67/3.09  #Close   : 0
% 7.67/3.09  
% 7.67/3.09  Ordering : KBO
% 7.67/3.09  
% 7.67/3.09  Simplification rules
% 7.67/3.09  ----------------------
% 7.67/3.09  #Subsume      : 353
% 7.67/3.09  #Demod        : 127
% 7.67/3.09  #Tautology    : 131
% 7.67/3.09  #SimpNegUnit  : 354
% 7.67/3.09  #BackRed      : 0
% 7.67/3.09  
% 7.67/3.09  #Partial instantiations: 0
% 7.67/3.09  #Strategies tried      : 1
% 7.67/3.09  
% 7.67/3.09  Timing (in seconds)
% 7.67/3.09  ----------------------
% 7.67/3.09  Preprocessing        : 0.30
% 7.67/3.09  Parsing              : 0.16
% 7.67/3.09  CNF conversion       : 0.02
% 7.67/3.09  Main loop            : 2.03
% 7.67/3.09  Inferencing          : 0.53
% 7.67/3.09  Reduction            : 0.68
% 7.67/3.09  Demodulation         : 0.44
% 7.67/3.09  BG Simplification    : 0.05
% 7.67/3.09  Subsumption          : 0.62
% 7.67/3.09  Abstraction          : 0.06
% 7.67/3.09  MUC search           : 0.00
% 7.67/3.09  Cooper               : 0.00
% 7.67/3.09  Total                : 2.36
% 7.67/3.09  Index Insertion      : 0.00
% 7.67/3.09  Index Deletion       : 0.00
% 7.67/3.09  Index Matching       : 0.00
% 7.67/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
