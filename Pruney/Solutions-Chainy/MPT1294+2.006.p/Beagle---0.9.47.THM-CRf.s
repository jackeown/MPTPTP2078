%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:39 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   43 (  72 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 137 expanded)
%              Number of equality atoms :   27 (  82 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( ~ ( B != k1_xboole_0
              & k7_setfam_1(A,B) = k1_xboole_0 )
          & ~ ( k7_setfam_1(A,B) != k1_xboole_0
              & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(c_28,plain,
    ( k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_37,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_2])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [A_2] : m1_subset_1('#skF_3',k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_4])).

tff(c_75,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden('#skF_1'(A_47,B_48,C_49),C_49)
      | r2_hidden(k3_subset_1(A_47,'#skF_1'(A_47,B_48,C_49)),B_48)
      | k7_setfam_1(A_47,B_48) = C_49
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k1_zfmisc_1(A_47)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_176,plain,(
    ! [B_73,A_74,C_75] :
      ( ~ r1_tarski(B_73,k3_subset_1(A_74,'#skF_1'(A_74,B_73,C_75)))
      | r2_hidden('#skF_1'(A_74,B_73,C_75),C_75)
      | k7_setfam_1(A_74,B_73) = C_75
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k1_zfmisc_1(A_74)))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(A_74))) ) ),
    inference(resolution,[status(thm)],[c_75,c_24])).

tff(c_179,plain,(
    ! [A_74,C_75] :
      ( r2_hidden('#skF_1'(A_74,'#skF_3',C_75),C_75)
      | k7_setfam_1(A_74,'#skF_3') = C_75
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k1_zfmisc_1(A_74)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_74))) ) ),
    inference(resolution,[status(thm)],[c_39,c_176])).

tff(c_183,plain,(
    ! [A_76,C_77] :
      ( r2_hidden('#skF_1'(A_76,'#skF_3',C_77),C_77)
      | k7_setfam_1(A_76,'#skF_3') = C_77
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_179])).

tff(c_196,plain,(
    ! [A_78] :
      ( r2_hidden('#skF_1'(A_78,'#skF_3','#skF_3'),'#skF_3')
      | k7_setfam_1(A_78,'#skF_3') = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_38,c_183])).

tff(c_201,plain,(
    ! [A_78] :
      ( ~ r1_tarski('#skF_3','#skF_1'(A_78,'#skF_3','#skF_3'))
      | k7_setfam_1(A_78,'#skF_3') = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_196,c_24])).

tff(c_205,plain,(
    ! [A_78] : k7_setfam_1(A_78,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_201])).

tff(c_34,plain,
    ( k1_xboole_0 != '#skF_3'
    | k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_48,plain,(
    k7_setfam_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_37,c_34])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_48])).

tff(c_216,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_215,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_245,plain,(
    ! [A_89,B_90] :
      ( k7_setfam_1(A_89,B_90) != k1_xboole_0
      | k1_xboole_0 = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(k1_zfmisc_1(A_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_248,plain,
    ( k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_245])).

tff(c_255,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_248])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_216,c_255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  
% 2.25/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.25/1.32  
% 2.25/1.32  %Foreground sorts:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Background operators:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Foreground operators:
% 2.25/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.32  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.25/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.25/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.32  
% 2.25/1.33  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tops_2)).
% 2.25/1.33  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.25/1.33  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.25/1.33  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.25/1.33  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.25/1.33  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.25/1.33  tff(c_28, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.25/1.33  tff(c_37, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_28])).
% 2.25/1.33  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.25/1.33  tff(c_39, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_2])).
% 2.25/1.33  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.33  tff(c_38, plain, (![A_2]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_4])).
% 2.25/1.33  tff(c_75, plain, (![A_47, B_48, C_49]: (r2_hidden('#skF_1'(A_47, B_48, C_49), C_49) | r2_hidden(k3_subset_1(A_47, '#skF_1'(A_47, B_48, C_49)), B_48) | k7_setfam_1(A_47, B_48)=C_49 | ~m1_subset_1(C_49, k1_zfmisc_1(k1_zfmisc_1(A_47))) | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.25/1.33  tff(c_24, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.25/1.33  tff(c_176, plain, (![B_73, A_74, C_75]: (~r1_tarski(B_73, k3_subset_1(A_74, '#skF_1'(A_74, B_73, C_75))) | r2_hidden('#skF_1'(A_74, B_73, C_75), C_75) | k7_setfam_1(A_74, B_73)=C_75 | ~m1_subset_1(C_75, k1_zfmisc_1(k1_zfmisc_1(A_74))) | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(A_74))))), inference(resolution, [status(thm)], [c_75, c_24])).
% 2.25/1.33  tff(c_179, plain, (![A_74, C_75]: (r2_hidden('#skF_1'(A_74, '#skF_3', C_75), C_75) | k7_setfam_1(A_74, '#skF_3')=C_75 | ~m1_subset_1(C_75, k1_zfmisc_1(k1_zfmisc_1(A_74))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_74))))), inference(resolution, [status(thm)], [c_39, c_176])).
% 2.25/1.33  tff(c_183, plain, (![A_76, C_77]: (r2_hidden('#skF_1'(A_76, '#skF_3', C_77), C_77) | k7_setfam_1(A_76, '#skF_3')=C_77 | ~m1_subset_1(C_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_179])).
% 2.25/1.33  tff(c_196, plain, (![A_78]: (r2_hidden('#skF_1'(A_78, '#skF_3', '#skF_3'), '#skF_3') | k7_setfam_1(A_78, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_38, c_183])).
% 2.25/1.33  tff(c_201, plain, (![A_78]: (~r1_tarski('#skF_3', '#skF_1'(A_78, '#skF_3', '#skF_3')) | k7_setfam_1(A_78, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_196, c_24])).
% 2.25/1.33  tff(c_205, plain, (![A_78]: (k7_setfam_1(A_78, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_201])).
% 2.25/1.33  tff(c_34, plain, (k1_xboole_0!='#skF_3' | k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.25/1.33  tff(c_48, plain, (k7_setfam_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_37, c_37, c_34])).
% 2.25/1.33  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_48])).
% 2.25/1.33  tff(c_216, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 2.25/1.33  tff(c_215, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.25/1.33  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.25/1.33  tff(c_245, plain, (![A_89, B_90]: (k7_setfam_1(A_89, B_90)!=k1_xboole_0 | k1_xboole_0=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(k1_zfmisc_1(A_89))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.25/1.33  tff(c_248, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_26, c_245])).
% 2.25/1.33  tff(c_255, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_215, c_248])).
% 2.25/1.33  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_216, c_255])).
% 2.25/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.33  
% 2.25/1.33  Inference rules
% 2.25/1.33  ----------------------
% 2.25/1.33  #Ref     : 0
% 2.25/1.33  #Sup     : 42
% 2.25/1.33  #Fact    : 0
% 2.25/1.33  #Define  : 0
% 2.25/1.33  #Split   : 2
% 2.25/1.33  #Chain   : 0
% 2.25/1.33  #Close   : 0
% 2.25/1.33  
% 2.25/1.33  Ordering : KBO
% 2.25/1.33  
% 2.25/1.33  Simplification rules
% 2.25/1.33  ----------------------
% 2.25/1.33  #Subsume      : 3
% 2.25/1.33  #Demod        : 22
% 2.25/1.33  #Tautology    : 18
% 2.25/1.33  #SimpNegUnit  : 1
% 2.25/1.33  #BackRed      : 5
% 2.25/1.33  
% 2.25/1.33  #Partial instantiations: 0
% 2.25/1.33  #Strategies tried      : 1
% 2.25/1.33  
% 2.25/1.33  Timing (in seconds)
% 2.25/1.33  ----------------------
% 2.25/1.33  Preprocessing        : 0.31
% 2.25/1.33  Parsing              : 0.17
% 2.25/1.33  CNF conversion       : 0.02
% 2.25/1.33  Main loop            : 0.23
% 2.25/1.33  Inferencing          : 0.09
% 2.25/1.33  Reduction            : 0.06
% 2.25/1.33  Demodulation         : 0.04
% 2.25/1.33  BG Simplification    : 0.02
% 2.25/1.33  Subsumption          : 0.05
% 2.25/1.33  Abstraction          : 0.01
% 2.25/1.33  MUC search           : 0.00
% 2.25/1.33  Cooper               : 0.00
% 2.25/1.33  Total                : 0.56
% 2.25/1.33  Index Insertion      : 0.00
% 2.25/1.33  Index Deletion       : 0.00
% 2.25/1.33  Index Matching       : 0.00
% 2.25/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
