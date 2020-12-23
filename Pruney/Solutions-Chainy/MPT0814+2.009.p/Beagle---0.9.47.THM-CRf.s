%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:52 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   45 (  52 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 (  86 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_14,plain,(
    ! [A_6,B_7,D_33] :
      ( r2_hidden('#skF_6'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),A_6)
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_6,B_7,D_33] :
      ( k4_tarski('#skF_6'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33),'#skF_7'(A_6,B_7,k2_zfmisc_1(A_6,B_7),D_33)) = D_33
      | ~ r2_hidden(D_33,k2_zfmisc_1(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_118,plain,(
    ! [A_76,B_77,D_78] :
      ( r2_hidden('#skF_7'(A_76,B_77,k2_zfmisc_1(A_76,B_77),D_78),B_77)
      | ~ r2_hidden(D_78,k2_zfmisc_1(A_76,B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [F_45,E_44] :
      ( ~ r2_hidden(F_45,'#skF_10')
      | ~ r2_hidden(E_44,'#skF_9')
      | k4_tarski(E_44,F_45) != '#skF_8' ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_267,plain,(
    ! [E_125,A_126,D_127] :
      ( ~ r2_hidden(E_125,'#skF_9')
      | k4_tarski(E_125,'#skF_7'(A_126,'#skF_10',k2_zfmisc_1(A_126,'#skF_10'),D_127)) != '#skF_8'
      | ~ r2_hidden(D_127,k2_zfmisc_1(A_126,'#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_118,c_36])).

tff(c_949,plain,(
    ! [A_252,D_253] :
      ( ~ r2_hidden('#skF_6'(A_252,'#skF_10',k2_zfmisc_1(A_252,'#skF_10'),D_253),'#skF_9')
      | D_253 != '#skF_8'
      | ~ r2_hidden(D_253,k2_zfmisc_1(A_252,'#skF_10'))
      | ~ r2_hidden(D_253,k2_zfmisc_1(A_252,'#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_267])).

tff(c_960,plain,(
    ~ r2_hidden('#skF_8',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_14,c_949])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_52,B_53] :
      ( ~ r2_hidden('#skF_1'(A_52,B_53),B_53)
      | r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_40,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_50,plain,(
    r1_tarski('#skF_11',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_40,c_42])).

tff(c_38,plain,(
    r2_hidden('#skF_8','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_59,plain,(
    ! [C_55,B_56,A_57] :
      ( r2_hidden(C_55,B_56)
      | ~ r2_hidden(C_55,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [B_60] :
      ( r2_hidden('#skF_8',B_60)
      | ~ r1_tarski('#skF_11',B_60) ) ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [B_61,B_62] :
      ( r2_hidden('#skF_8',B_61)
      | ~ r1_tarski(B_62,B_61)
      | ~ r1_tarski('#skF_11',B_62) ) ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_83,plain,
    ( r2_hidden('#skF_8',k2_zfmisc_1('#skF_9','#skF_10'))
    | ~ r1_tarski('#skF_11','#skF_11') ),
    inference(resolution,[status(thm)],[c_50,c_79])).

tff(c_87,plain,(
    r2_hidden('#skF_8',k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_83])).

tff(c_962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_960,c_87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:41:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.60  
% 3.48/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.48/1.60  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_11 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1
% 3.48/1.60  
% 3.48/1.60  %Foreground sorts:
% 3.48/1.60  
% 3.48/1.60  
% 3.48/1.60  %Background operators:
% 3.48/1.60  
% 3.48/1.60  
% 3.48/1.60  %Foreground operators:
% 3.48/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.60  tff('#skF_11', type, '#skF_11': $i).
% 3.48/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.48/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.48/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.60  tff('#skF_10', type, '#skF_10': $i).
% 3.48/1.60  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.48/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.48/1.60  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.48/1.60  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.48/1.60  tff('#skF_9', type, '#skF_9': $i).
% 3.48/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.48/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.48/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.48/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.48/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.60  
% 3.79/1.61  tff(f_44, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.79/1.61  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 3.79/1.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.79/1.61  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.79/1.61  tff(c_14, plain, (![A_6, B_7, D_33]: (r2_hidden('#skF_6'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), A_6) | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.79/1.61  tff(c_10, plain, (![A_6, B_7, D_33]: (k4_tarski('#skF_6'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33), '#skF_7'(A_6, B_7, k2_zfmisc_1(A_6, B_7), D_33))=D_33 | ~r2_hidden(D_33, k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.79/1.61  tff(c_118, plain, (![A_76, B_77, D_78]: (r2_hidden('#skF_7'(A_76, B_77, k2_zfmisc_1(A_76, B_77), D_78), B_77) | ~r2_hidden(D_78, k2_zfmisc_1(A_76, B_77)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.79/1.61  tff(c_36, plain, (![F_45, E_44]: (~r2_hidden(F_45, '#skF_10') | ~r2_hidden(E_44, '#skF_9') | k4_tarski(E_44, F_45)!='#skF_8')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.79/1.61  tff(c_267, plain, (![E_125, A_126, D_127]: (~r2_hidden(E_125, '#skF_9') | k4_tarski(E_125, '#skF_7'(A_126, '#skF_10', k2_zfmisc_1(A_126, '#skF_10'), D_127))!='#skF_8' | ~r2_hidden(D_127, k2_zfmisc_1(A_126, '#skF_10')))), inference(resolution, [status(thm)], [c_118, c_36])).
% 3.79/1.61  tff(c_949, plain, (![A_252, D_253]: (~r2_hidden('#skF_6'(A_252, '#skF_10', k2_zfmisc_1(A_252, '#skF_10'), D_253), '#skF_9') | D_253!='#skF_8' | ~r2_hidden(D_253, k2_zfmisc_1(A_252, '#skF_10')) | ~r2_hidden(D_253, k2_zfmisc_1(A_252, '#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_10, c_267])).
% 3.79/1.61  tff(c_960, plain, (~r2_hidden('#skF_8', k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_14, c_949])).
% 3.79/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.79/1.61  tff(c_52, plain, (![A_52, B_53]: (~r2_hidden('#skF_1'(A_52, B_53), B_53) | r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.79/1.61  tff(c_57, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_52])).
% 3.79/1.61  tff(c_40, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.79/1.61  tff(c_42, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.79/1.61  tff(c_50, plain, (r1_tarski('#skF_11', k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_40, c_42])).
% 3.79/1.61  tff(c_38, plain, (r2_hidden('#skF_8', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.79/1.61  tff(c_59, plain, (![C_55, B_56, A_57]: (r2_hidden(C_55, B_56) | ~r2_hidden(C_55, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.79/1.61  tff(c_71, plain, (![B_60]: (r2_hidden('#skF_8', B_60) | ~r1_tarski('#skF_11', B_60))), inference(resolution, [status(thm)], [c_38, c_59])).
% 3.79/1.61  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.79/1.61  tff(c_79, plain, (![B_61, B_62]: (r2_hidden('#skF_8', B_61) | ~r1_tarski(B_62, B_61) | ~r1_tarski('#skF_11', B_62))), inference(resolution, [status(thm)], [c_71, c_2])).
% 3.79/1.61  tff(c_83, plain, (r2_hidden('#skF_8', k2_zfmisc_1('#skF_9', '#skF_10')) | ~r1_tarski('#skF_11', '#skF_11')), inference(resolution, [status(thm)], [c_50, c_79])).
% 3.79/1.61  tff(c_87, plain, (r2_hidden('#skF_8', k2_zfmisc_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_83])).
% 3.79/1.61  tff(c_962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_960, c_87])).
% 3.79/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.61  
% 3.79/1.61  Inference rules
% 3.79/1.61  ----------------------
% 3.79/1.61  #Ref     : 0
% 3.79/1.61  #Sup     : 262
% 3.79/1.61  #Fact    : 0
% 3.79/1.61  #Define  : 0
% 3.79/1.61  #Split   : 12
% 3.79/1.61  #Chain   : 0
% 3.79/1.61  #Close   : 0
% 3.79/1.61  
% 3.79/1.61  Ordering : KBO
% 3.79/1.61  
% 3.79/1.61  Simplification rules
% 3.79/1.61  ----------------------
% 3.79/1.61  #Subsume      : 31
% 3.79/1.61  #Demod        : 4
% 3.79/1.61  #Tautology    : 9
% 3.79/1.61  #SimpNegUnit  : 1
% 3.79/1.61  #BackRed      : 1
% 3.79/1.61  
% 3.79/1.61  #Partial instantiations: 0
% 3.79/1.61  #Strategies tried      : 1
% 3.79/1.61  
% 3.79/1.61  Timing (in seconds)
% 3.79/1.61  ----------------------
% 3.79/1.61  Preprocessing        : 0.28
% 3.79/1.61  Parsing              : 0.15
% 3.79/1.61  CNF conversion       : 0.02
% 3.79/1.62  Main loop            : 0.58
% 3.79/1.62  Inferencing          : 0.18
% 3.79/1.62  Reduction            : 0.13
% 3.79/1.62  Demodulation         : 0.09
% 3.79/1.62  BG Simplification    : 0.03
% 3.79/1.62  Subsumption          : 0.21
% 3.79/1.62  Abstraction          : 0.03
% 3.79/1.62  MUC search           : 0.00
% 3.79/1.62  Cooper               : 0.00
% 3.79/1.62  Total                : 0.89
% 3.79/1.62  Index Insertion      : 0.00
% 3.79/1.62  Index Deletion       : 0.00
% 3.79/1.62  Index Matching       : 0.00
% 3.79/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
