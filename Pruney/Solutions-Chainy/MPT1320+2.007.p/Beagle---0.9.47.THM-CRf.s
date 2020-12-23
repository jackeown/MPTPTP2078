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
% DateTime   : Thu Dec  3 10:23:07 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   65 (  95 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_tops_2 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_tops_2,type,(
    k1_tops_2: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
                   => ( r2_hidden(B,D)
                     => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),k1_tops_2(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) )
     => m1_subset_1(k1_tops_2(A,B,C),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => m1_subset_1(k9_subset_1(u1_struct_0(A),B,C),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,C)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B)))))
                 => ( D = k1_tops_2(A,B,C)
                  <=> ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(k1_pre_topc(A,B))))
                       => ( r2_hidden(E,D)
                        <=> ? [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(A)))
                              & r2_hidden(F,C)
                              & k9_subset_1(u1_struct_0(A),F,B) = E ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_2)).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ! [A_173,B_174,C_175] :
      ( m1_subset_1(k1_tops_2(A_173,B_174,C_175),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_173,B_174)))))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_173))))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [A_176,B_180,C_182] :
      ( m1_subset_1(k9_subset_1(u1_struct_0(A_176),B_180,C_182),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_176,C_182))))
      | ~ m1_subset_1(C_182,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_88,plain,(
    ! [A_246,F_247,B_248,C_249] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_246),F_247,B_248),k1_tops_2(A_246,B_248,C_249))
      | ~ r2_hidden(F_247,C_249)
      | ~ m1_subset_1(F_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(A_246),F_247,B_248),k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_246,B_248))))
      | ~ m1_subset_1(k1_tops_2(A_246,B_248,C_249),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_246,B_248)))))
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_246))))
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_92,plain,(
    ! [A_250,B_251,C_252,C_253] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_250),B_251,C_252),k1_tops_2(A_250,C_252,C_253))
      | ~ r2_hidden(B_251,C_253)
      | ~ m1_subset_1(k1_tops_2(A_250,C_252,C_253),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_250,C_252)))))
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_250))))
      | ~ m1_subset_1(C_252,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ m1_subset_1(B_251,k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ l1_pre_topc(A_250) ) ),
    inference(resolution,[status(thm)],[c_30,c_88])).

tff(c_96,plain,(
    ! [A_254,B_255,B_256,C_257] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_254),B_255,B_256),k1_tops_2(A_254,B_256,C_257))
      | ~ r2_hidden(B_255,C_257)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_254))))
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_254)))
      | ~ l1_pre_topc(A_254) ) ),
    inference(resolution,[status(thm)],[c_28,c_92])).

tff(c_32,plain,(
    ~ r2_hidden(k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_6'),k1_tops_2('#skF_4','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_99,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_32])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_40,c_34,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:04:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.27  
% 2.38/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.27  %$ r2_hidden > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_tops_2 > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4 > #skF_3
% 2.38/1.27  
% 2.38/1.27  %Foreground sorts:
% 2.38/1.27  
% 2.38/1.27  
% 2.38/1.27  %Background operators:
% 2.38/1.27  
% 2.38/1.27  
% 2.38/1.27  %Foreground operators:
% 2.38/1.27  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.38/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.38/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.38/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.38/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.27  tff(k1_tops_2, type, k1_tops_2: ($i * $i * $i) > $i).
% 2.38/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.38/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.38/1.27  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.38/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.27  
% 2.38/1.28  tff(f_84, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r2_hidden(B, D) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), k1_tops_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_2)).
% 2.38/1.28  tff(f_58, axiom, (![A, B, C]: (((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))) => m1_subset_1(k1_tops_2(A, B, C), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 2.38/1.28  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => m1_subset_1(k9_subset_1(u1_struct_0(A), B, C), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_tops_2)).
% 2.38/1.28  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B))))) => ((D = k1_tops_2(A, B, C)) <=> (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(k1_pre_topc(A, B)))) => (r2_hidden(E, D) <=> (?[F]: ((m1_subset_1(F, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(F, C)) & (k9_subset_1(u1_struct_0(A), F, B) = E))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_2)).
% 2.38/1.28  tff(c_42, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.28  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.28  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.28  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.28  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.28  tff(c_28, plain, (![A_173, B_174, C_175]: (m1_subset_1(k1_tops_2(A_173, B_174, C_175), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_173, B_174))))) | ~m1_subset_1(C_175, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_173)))) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.38/1.28  tff(c_30, plain, (![A_176, B_180, C_182]: (m1_subset_1(k9_subset_1(u1_struct_0(A_176), B_180, C_182), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_176, C_182)))) | ~m1_subset_1(C_182, k1_zfmisc_1(u1_struct_0(A_176))) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.38/1.28  tff(c_88, plain, (![A_246, F_247, B_248, C_249]: (r2_hidden(k9_subset_1(u1_struct_0(A_246), F_247, B_248), k1_tops_2(A_246, B_248, C_249)) | ~r2_hidden(F_247, C_249) | ~m1_subset_1(F_247, k1_zfmisc_1(u1_struct_0(A_246))) | ~m1_subset_1(k9_subset_1(u1_struct_0(A_246), F_247, B_248), k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_246, B_248)))) | ~m1_subset_1(k1_tops_2(A_246, B_248, C_249), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_246, B_248))))) | ~m1_subset_1(C_249, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_246)))) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.38/1.28  tff(c_92, plain, (![A_250, B_251, C_252, C_253]: (r2_hidden(k9_subset_1(u1_struct_0(A_250), B_251, C_252), k1_tops_2(A_250, C_252, C_253)) | ~r2_hidden(B_251, C_253) | ~m1_subset_1(k1_tops_2(A_250, C_252, C_253), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(A_250, C_252))))) | ~m1_subset_1(C_253, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_250)))) | ~m1_subset_1(C_252, k1_zfmisc_1(u1_struct_0(A_250))) | ~m1_subset_1(B_251, k1_zfmisc_1(u1_struct_0(A_250))) | ~l1_pre_topc(A_250))), inference(resolution, [status(thm)], [c_30, c_88])).
% 2.38/1.28  tff(c_96, plain, (![A_254, B_255, B_256, C_257]: (r2_hidden(k9_subset_1(u1_struct_0(A_254), B_255, B_256), k1_tops_2(A_254, B_256, C_257)) | ~r2_hidden(B_255, C_257) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0(A_254))) | ~m1_subset_1(C_257, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_254)))) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_254))) | ~l1_pre_topc(A_254))), inference(resolution, [status(thm)], [c_28, c_92])).
% 2.38/1.28  tff(c_32, plain, (~r2_hidden(k9_subset_1(u1_struct_0('#skF_4'), '#skF_5', '#skF_6'), k1_tops_2('#skF_4', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.28  tff(c_99, plain, (~r2_hidden('#skF_5', '#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_96, c_32])).
% 2.38/1.28  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_40, c_34, c_99])).
% 2.38/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.28  
% 2.38/1.28  Inference rules
% 2.38/1.28  ----------------------
% 2.38/1.28  #Ref     : 0
% 2.38/1.28  #Sup     : 13
% 2.38/1.28  #Fact    : 0
% 2.38/1.28  #Define  : 0
% 2.38/1.29  #Split   : 0
% 2.38/1.29  #Chain   : 0
% 2.38/1.29  #Close   : 0
% 2.38/1.29  
% 2.38/1.29  Ordering : KBO
% 2.38/1.29  
% 2.38/1.29  Simplification rules
% 2.38/1.29  ----------------------
% 2.38/1.29  #Subsume      : 3
% 2.38/1.29  #Demod        : 5
% 2.38/1.29  #Tautology    : 1
% 2.38/1.29  #SimpNegUnit  : 0
% 2.38/1.29  #BackRed      : 0
% 2.38/1.29  
% 2.38/1.29  #Partial instantiations: 0
% 2.38/1.29  #Strategies tried      : 1
% 2.38/1.29  
% 2.38/1.29  Timing (in seconds)
% 2.38/1.29  ----------------------
% 2.38/1.29  Preprocessing        : 0.33
% 2.38/1.29  Parsing              : 0.16
% 2.38/1.29  CNF conversion       : 0.04
% 2.38/1.29  Main loop            : 0.20
% 2.38/1.29  Inferencing          : 0.08
% 2.38/1.29  Reduction            : 0.05
% 2.38/1.29  Demodulation         : 0.04
% 2.38/1.29  BG Simplification    : 0.02
% 2.38/1.29  Subsumption          : 0.04
% 2.38/1.29  Abstraction          : 0.01
% 2.38/1.29  MUC search           : 0.00
% 2.38/1.29  Cooper               : 0.00
% 2.38/1.29  Total                : 0.56
% 2.38/1.29  Index Insertion      : 0.00
% 2.38/1.29  Index Deletion       : 0.00
% 2.38/1.29  Index Matching       : 0.00
% 2.38/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
