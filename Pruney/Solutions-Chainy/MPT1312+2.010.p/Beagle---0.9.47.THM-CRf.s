%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:58 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   60 (  96 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 167 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_83,plain,(
    ! [B_66,A_67] :
      ( l1_pre_topc(B_66)
      | ~ m1_pre_topc(B_66,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_86,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_83])).

tff(c_89,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_86])).

tff(c_136,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(k2_struct_0(B_77),k2_struct_0(A_78))
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(B_77)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_zfmisc_1(A_6),k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    ! [A_51] :
      ( l1_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_93,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_89,c_58])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_69,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    r1_tarski('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_48,c_69])).

tff(c_94,plain,(
    ! [A_68,B_69] :
      ( k2_xboole_0(A_68,B_69) = B_69
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_98,plain,(
    k2_xboole_0('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) = k1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_73,c_94])).

tff(c_114,plain,(
    k2_xboole_0('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_5'))) = k1_zfmisc_1(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_98])).

tff(c_124,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_tarski(A_72,C_73)
      | ~ r1_tarski(k2_xboole_0(A_72,B_74),C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [C_75] :
      ( r1_tarski('#skF_6',C_75)
      | ~ r1_tarski(k1_zfmisc_1(k2_struct_0('#skF_5')),C_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_124])).

tff(c_134,plain,(
    ! [B_7] :
      ( r1_tarski('#skF_6',k1_zfmisc_1(B_7))
      | ~ r1_tarski(k2_struct_0('#skF_5'),B_7) ) ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_140,plain,(
    ! [A_78] :
      ( r1_tarski('#skF_6',k1_zfmisc_1(k2_struct_0(A_78)))
      | ~ m1_pre_topc('#skF_5',A_78)
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_136,c_134])).

tff(c_160,plain,(
    ! [A_81] :
      ( r1_tarski('#skF_6',k1_zfmisc_1(k2_struct_0(A_81)))
      | ~ m1_pre_topc('#skF_5',A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_140])).

tff(c_74,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(A_64,k1_zfmisc_1(B_65))
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_59,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(resolution,[status(thm)],[c_42,c_54])).

tff(c_63,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_59])).

tff(c_46,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_64,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_46])).

tff(c_82,plain,(
    ~ r1_tarski('#skF_6',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_74,c_64])).

tff(c_166,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_160,c_82])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.26  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.10/1.26  
% 2.10/1.26  %Foreground sorts:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Background operators:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Foreground operators:
% 2.10/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.10/1.26  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.10/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.10/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.10/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.26  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.10/1.26  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.10/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.10/1.26  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.10/1.26  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.10/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.26  
% 2.10/1.28  tff(f_88, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 2.10/1.28  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.10/1.28  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 2.10/1.28  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.10/1.28  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.10/1.28  tff(f_45, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.10/1.28  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.10/1.28  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.10/1.28  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.10/1.28  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.10/1.28  tff(c_50, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.10/1.28  tff(c_83, plain, (![B_66, A_67]: (l1_pre_topc(B_66) | ~m1_pre_topc(B_66, A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.10/1.28  tff(c_86, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_83])).
% 2.10/1.28  tff(c_89, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_86])).
% 2.10/1.28  tff(c_136, plain, (![B_77, A_78]: (r1_tarski(k2_struct_0(B_77), k2_struct_0(A_78)) | ~m1_pre_topc(B_77, A_78) | ~l1_pre_topc(B_77) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.10/1.28  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k1_zfmisc_1(A_6), k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.28  tff(c_42, plain, (![A_51]: (l1_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.10/1.28  tff(c_54, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.28  tff(c_58, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_42, c_54])).
% 2.10/1.28  tff(c_93, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_89, c_58])).
% 2.10/1.28  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.10/1.28  tff(c_69, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.28  tff(c_73, plain, (r1_tarski('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_48, c_69])).
% 2.10/1.28  tff(c_94, plain, (![A_68, B_69]: (k2_xboole_0(A_68, B_69)=B_69 | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.28  tff(c_98, plain, (k2_xboole_0('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))=k1_zfmisc_1(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_73, c_94])).
% 2.10/1.28  tff(c_114, plain, (k2_xboole_0('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_5')))=k1_zfmisc_1(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_98])).
% 2.10/1.28  tff(c_124, plain, (![A_72, C_73, B_74]: (r1_tarski(A_72, C_73) | ~r1_tarski(k2_xboole_0(A_72, B_74), C_73))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.28  tff(c_129, plain, (![C_75]: (r1_tarski('#skF_6', C_75) | ~r1_tarski(k1_zfmisc_1(k2_struct_0('#skF_5')), C_75))), inference(superposition, [status(thm), theory('equality')], [c_114, c_124])).
% 2.10/1.28  tff(c_134, plain, (![B_7]: (r1_tarski('#skF_6', k1_zfmisc_1(B_7)) | ~r1_tarski(k2_struct_0('#skF_5'), B_7))), inference(resolution, [status(thm)], [c_6, c_129])).
% 2.10/1.28  tff(c_140, plain, (![A_78]: (r1_tarski('#skF_6', k1_zfmisc_1(k2_struct_0(A_78))) | ~m1_pre_topc('#skF_5', A_78) | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_136, c_134])).
% 2.10/1.28  tff(c_160, plain, (![A_81]: (r1_tarski('#skF_6', k1_zfmisc_1(k2_struct_0(A_81))) | ~m1_pre_topc('#skF_5', A_81) | ~l1_pre_topc(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_140])).
% 2.10/1.28  tff(c_74, plain, (![A_64, B_65]: (m1_subset_1(A_64, k1_zfmisc_1(B_65)) | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.28  tff(c_59, plain, (![A_61]: (u1_struct_0(A_61)=k2_struct_0(A_61) | ~l1_pre_topc(A_61))), inference(resolution, [status(thm)], [c_42, c_54])).
% 2.10/1.28  tff(c_63, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_59])).
% 2.10/1.28  tff(c_46, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.10/1.28  tff(c_64, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_46])).
% 2.10/1.28  tff(c_82, plain, (~r1_tarski('#skF_6', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_74, c_64])).
% 2.10/1.28  tff(c_166, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_160, c_82])).
% 2.10/1.28  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_166])).
% 2.10/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.28  
% 2.10/1.28  Inference rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Ref     : 0
% 2.10/1.28  #Sup     : 26
% 2.10/1.28  #Fact    : 0
% 2.10/1.28  #Define  : 0
% 2.10/1.28  #Split   : 0
% 2.10/1.28  #Chain   : 0
% 2.10/1.28  #Close   : 0
% 2.10/1.28  
% 2.10/1.28  Ordering : KBO
% 2.10/1.28  
% 2.10/1.28  Simplification rules
% 2.10/1.28  ----------------------
% 2.10/1.28  #Subsume      : 0
% 2.10/1.28  #Demod        : 11
% 2.10/1.28  #Tautology    : 12
% 2.10/1.28  #SimpNegUnit  : 0
% 2.10/1.28  #BackRed      : 3
% 2.10/1.28  
% 2.10/1.28  #Partial instantiations: 0
% 2.10/1.28  #Strategies tried      : 1
% 2.10/1.28  
% 2.10/1.28  Timing (in seconds)
% 2.10/1.28  ----------------------
% 2.10/1.28  Preprocessing        : 0.35
% 2.10/1.28  Parsing              : 0.17
% 2.10/1.28  CNF conversion       : 0.03
% 2.10/1.28  Main loop            : 0.16
% 2.10/1.28  Inferencing          : 0.05
% 2.10/1.28  Reduction            : 0.05
% 2.10/1.28  Demodulation         : 0.04
% 2.10/1.28  BG Simplification    : 0.02
% 2.10/1.28  Subsumption          : 0.03
% 2.10/1.28  Abstraction          : 0.01
% 2.10/1.28  MUC search           : 0.00
% 2.10/1.28  Cooper               : 0.00
% 2.10/1.28  Total                : 0.54
% 2.10/1.28  Index Insertion      : 0.00
% 2.10/1.28  Index Deletion       : 0.00
% 2.10/1.28  Index Matching       : 0.00
% 2.10/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
