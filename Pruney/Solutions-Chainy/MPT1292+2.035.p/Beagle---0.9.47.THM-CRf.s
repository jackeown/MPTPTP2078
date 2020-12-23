%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:33 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   66 (  91 expanded)
%              Number of leaves         :   33 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 144 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k3_mcart_1 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_85,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( m1_setfam_1(B,A)
      <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_48,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_56,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_44,plain,(
    m1_setfam_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_18,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_54,plain,(
    ! [A_7] : m1_subset_1('#skF_5',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_126,plain,(
    ! [A_60,B_61] :
      ( k5_setfam_1(A_60,B_61) = k3_tarski(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_131,plain,(
    ! [A_60] : k5_setfam_1(A_60,'#skF_5') = k3_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_126])).

tff(c_150,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k5_setfam_1(A_66,B_67),k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_162,plain,(
    ! [A_60] :
      ( m1_subset_1(k3_tarski('#skF_5'),k1_zfmisc_1(A_60))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_150])).

tff(c_168,plain,(
    ! [A_68] : m1_subset_1(k3_tarski('#skF_5'),k1_zfmisc_1(A_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_162])).

tff(c_16,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_87,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,B_51)
      | v1_xboole_0(B_51)
      | ~ m1_subset_1(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [A_50,A_1] :
      ( r1_tarski(A_50,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_50,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_97,plain,(
    ! [A_50,A_1] :
      ( r1_tarski(A_50,A_1)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_91])).

tff(c_191,plain,(
    ! [A_73] : r1_tarski(k3_tarski('#skF_5'),A_73) ),
    inference(resolution,[status(thm)],[c_168,c_97])).

tff(c_34,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_3'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_64,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_3'(A_41),A_41)
      | A_41 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34])).

tff(c_32,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_68,plain,(
    ! [A_41] :
      ( ~ r1_tarski(A_41,'#skF_3'(A_41))
      | A_41 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_64,c_32])).

tff(c_200,plain,(
    k3_tarski('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_191,c_68])).

tff(c_203,plain,(
    ! [A_60] : k5_setfam_1(A_60,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_131])).

tff(c_222,plain,(
    ! [A_75,B_76] :
      ( k5_setfam_1(A_75,B_76) = A_75
      | ~ m1_setfam_1(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_230,plain,(
    ! [A_75] :
      ( k5_setfam_1(A_75,'#skF_5') = A_75
      | ~ m1_setfam_1('#skF_5',A_75) ) ),
    inference(resolution,[status(thm)],[c_54,c_222])).

tff(c_234,plain,(
    ! [A_77] :
      ( A_77 = '#skF_5'
      | ~ m1_setfam_1('#skF_5',A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_230])).

tff(c_238,plain,(
    u1_struct_0('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_234])).

tff(c_40,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(u1_struct_0(A_35))
      | ~ l1_struct_0(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_243,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_40])).

tff(c_247,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_56,c_243])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k3_mcart_1 > k5_setfam_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.08/1.28  
% 2.08/1.28  %Foreground sorts:
% 2.08/1.28  
% 2.08/1.28  
% 2.08/1.28  %Background operators:
% 2.08/1.28  
% 2.08/1.28  
% 2.08/1.28  %Foreground operators:
% 2.08/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.28  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.08/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.28  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.08/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.08/1.28  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.08/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.28  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.08/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.08/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.28  
% 2.08/1.30  tff(f_107, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_tops_2)).
% 2.08/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.08/1.30  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.08/1.30  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.08/1.30  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.08/1.30  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.08/1.30  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.08/1.30  tff(f_33, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.08/1.30  tff(f_85, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 2.08/1.30  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.08/1.30  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.08/1.30  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.08/1.30  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.08/1.30  tff(c_48, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.08/1.30  tff(c_42, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.08/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.08/1.30  tff(c_56, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2])).
% 2.08/1.30  tff(c_44, plain, (m1_setfam_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.08/1.30  tff(c_18, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.08/1.30  tff(c_54, plain, (![A_7]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 2.08/1.30  tff(c_126, plain, (![A_60, B_61]: (k5_setfam_1(A_60, B_61)=k3_tarski(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.08/1.30  tff(c_131, plain, (![A_60]: (k5_setfam_1(A_60, '#skF_5')=k3_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_126])).
% 2.08/1.30  tff(c_150, plain, (![A_66, B_67]: (m1_subset_1(k5_setfam_1(A_66, B_67), k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.08/1.30  tff(c_162, plain, (![A_60]: (m1_subset_1(k3_tarski('#skF_5'), k1_zfmisc_1(A_60)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(superposition, [status(thm), theory('equality')], [c_131, c_150])).
% 2.08/1.30  tff(c_168, plain, (![A_68]: (m1_subset_1(k3_tarski('#skF_5'), k1_zfmisc_1(A_68)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_162])).
% 2.08/1.30  tff(c_16, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.08/1.30  tff(c_87, plain, (![A_50, B_51]: (r2_hidden(A_50, B_51) | v1_xboole_0(B_51) | ~m1_subset_1(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.30  tff(c_4, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.30  tff(c_91, plain, (![A_50, A_1]: (r1_tarski(A_50, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_50, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_87, c_4])).
% 2.08/1.30  tff(c_97, plain, (![A_50, A_1]: (r1_tarski(A_50, A_1) | ~m1_subset_1(A_50, k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_16, c_91])).
% 2.08/1.30  tff(c_191, plain, (![A_73]: (r1_tarski(k3_tarski('#skF_5'), A_73))), inference(resolution, [status(thm)], [c_168, c_97])).
% 2.08/1.30  tff(c_34, plain, (![A_21]: (r2_hidden('#skF_3'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.08/1.30  tff(c_64, plain, (![A_41]: (r2_hidden('#skF_3'(A_41), A_41) | A_41='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34])).
% 2.08/1.30  tff(c_32, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.08/1.30  tff(c_68, plain, (![A_41]: (~r1_tarski(A_41, '#skF_3'(A_41)) | A_41='#skF_5')), inference(resolution, [status(thm)], [c_64, c_32])).
% 2.08/1.30  tff(c_200, plain, (k3_tarski('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_191, c_68])).
% 2.08/1.30  tff(c_203, plain, (![A_60]: (k5_setfam_1(A_60, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_131])).
% 2.08/1.30  tff(c_222, plain, (![A_75, B_76]: (k5_setfam_1(A_75, B_76)=A_75 | ~m1_setfam_1(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(A_75))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.30  tff(c_230, plain, (![A_75]: (k5_setfam_1(A_75, '#skF_5')=A_75 | ~m1_setfam_1('#skF_5', A_75))), inference(resolution, [status(thm)], [c_54, c_222])).
% 2.08/1.30  tff(c_234, plain, (![A_77]: (A_77='#skF_5' | ~m1_setfam_1('#skF_5', A_77))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_230])).
% 2.08/1.30  tff(c_238, plain, (u1_struct_0('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_44, c_234])).
% 2.08/1.30  tff(c_40, plain, (![A_35]: (~v1_xboole_0(u1_struct_0(A_35)) | ~l1_struct_0(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.30  tff(c_243, plain, (~v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_238, c_40])).
% 2.08/1.30  tff(c_247, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_56, c_243])).
% 2.08/1.30  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_247])).
% 2.08/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.30  
% 2.08/1.30  Inference rules
% 2.08/1.30  ----------------------
% 2.08/1.30  #Ref     : 0
% 2.08/1.30  #Sup     : 41
% 2.08/1.30  #Fact    : 0
% 2.08/1.30  #Define  : 0
% 2.08/1.30  #Split   : 0
% 2.08/1.30  #Chain   : 0
% 2.08/1.30  #Close   : 0
% 2.08/1.30  
% 2.08/1.30  Ordering : KBO
% 2.08/1.30  
% 2.08/1.30  Simplification rules
% 2.08/1.30  ----------------------
% 2.08/1.30  #Subsume      : 0
% 2.08/1.30  #Demod        : 20
% 2.08/1.30  #Tautology    : 18
% 2.08/1.30  #SimpNegUnit  : 2
% 2.08/1.30  #BackRed      : 4
% 2.08/1.30  
% 2.08/1.30  #Partial instantiations: 0
% 2.08/1.30  #Strategies tried      : 1
% 2.08/1.30  
% 2.08/1.30  Timing (in seconds)
% 2.08/1.30  ----------------------
% 2.27/1.30  Preprocessing        : 0.30
% 2.27/1.30  Parsing              : 0.16
% 2.27/1.30  CNF conversion       : 0.02
% 2.27/1.30  Main loop            : 0.17
% 2.27/1.30  Inferencing          : 0.06
% 2.27/1.30  Reduction            : 0.05
% 2.27/1.30  Demodulation         : 0.04
% 2.27/1.30  BG Simplification    : 0.01
% 2.27/1.30  Subsumption          : 0.02
% 2.27/1.30  Abstraction          : 0.01
% 2.27/1.30  MUC search           : 0.00
% 2.27/1.30  Cooper               : 0.00
% 2.27/1.30  Total                : 0.51
% 2.27/1.30  Index Insertion      : 0.00
% 2.27/1.30  Index Deletion       : 0.00
% 2.27/1.30  Index Matching       : 0.00
% 2.27/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
