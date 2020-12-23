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
% DateTime   : Thu Dec  3 09:57:45 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   33 (  71 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :   73 ( 232 expanded)
%              Number of equality atoms :   16 (  46 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

tff(c_12,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_1,B_2,C_6] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_6),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | C_6 = B_2
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_23,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1('#skF_1'(A_15,B_16,C_17),A_15)
      | C_17 = B_16
      | ~ m1_subset_1(C_17,k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [D_12] :
      ( r2_hidden(D_12,'#skF_4')
      | ~ r2_hidden(D_12,'#skF_3')
      | ~ m1_subset_1(D_12,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    ! [B_24,C_25] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),B_24,C_25),'#skF_4')
      | ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),B_24,C_25),'#skF_3')
      | C_25 = B_24
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_23,c_20])).

tff(c_60,plain,(
    ! [C_6] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3',C_6),'#skF_4')
      | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3',C_6),C_6)
      | C_6 = '#skF_3'
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_10,c_56])).

tff(c_67,plain,(
    ! [C_6] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3',C_6),'#skF_4')
      | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3',C_6),C_6)
      | C_6 = '#skF_3'
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_60])).

tff(c_93,plain,
    ( '#skF_3' = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(factorization,[status(thm),theory(equality)],[c_67])).

tff(c_96,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_93])).

tff(c_97,plain,(
    r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_96])).

tff(c_18,plain,(
    ! [D_12] :
      ( r2_hidden(D_12,'#skF_3')
      | ~ r2_hidden(D_12,'#skF_4')
      | ~ m1_subset_1(D_12,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_33,plain,(
    ! [B_16,C_17] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),B_16,C_17),'#skF_3')
      | ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),B_16,C_17),'#skF_4')
      | C_17 = B_16
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_23,c_18])).

tff(c_4,plain,(
    ! [A_1,B_2,C_6] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | ~ r2_hidden('#skF_1'(A_1,B_2,C_6),B_2)
      | C_6 = B_2
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,
    ( ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_97,c_4])).

tff(c_121,plain,
    ( ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_118])).

tff(c_122,plain,(
    ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_121])).

tff(c_126,plain,
    ( ~ r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_33,c_122])).

tff(c_132,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_97,c_126])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:41:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.26  
% 1.79/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.26  %$ r2_hidden > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.79/1.26  
% 1.79/1.26  %Foreground sorts:
% 1.79/1.26  
% 1.79/1.26  
% 1.79/1.26  %Background operators:
% 1.79/1.26  
% 1.79/1.26  
% 1.79/1.26  %Foreground operators:
% 1.79/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.79/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.79/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.26  
% 1.79/1.27  tff(f_54, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 1.79/1.27  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_subset_1)).
% 1.79/1.27  tff(c_12, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.27  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.27  tff(c_14, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.27  tff(c_10, plain, (![A_1, B_2, C_6]: (r2_hidden('#skF_1'(A_1, B_2, C_6), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | C_6=B_2 | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.27  tff(c_23, plain, (![A_15, B_16, C_17]: (m1_subset_1('#skF_1'(A_15, B_16, C_17), A_15) | C_17=B_16 | ~m1_subset_1(C_17, k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.27  tff(c_20, plain, (![D_12]: (r2_hidden(D_12, '#skF_4') | ~r2_hidden(D_12, '#skF_3') | ~m1_subset_1(D_12, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.27  tff(c_56, plain, (![B_24, C_25]: (r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), B_24, C_25), '#skF_4') | ~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), B_24, C_25), '#skF_3') | C_25=B_24 | ~m1_subset_1(C_25, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_23, c_20])).
% 1.79/1.27  tff(c_60, plain, (![C_6]: (r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', C_6), '#skF_4') | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', C_6), C_6) | C_6='#skF_3' | ~m1_subset_1(C_6, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_10, c_56])).
% 1.79/1.27  tff(c_67, plain, (![C_6]: (r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', C_6), '#skF_4') | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', C_6), C_6) | C_6='#skF_3' | ~m1_subset_1(C_6, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_60])).
% 1.79/1.27  tff(c_93, plain, ('#skF_3'='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(factorization, [status(thm), theory('equality')], [c_67])).
% 1.79/1.27  tff(c_96, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_93])).
% 1.79/1.27  tff(c_97, plain, (r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_12, c_96])).
% 1.79/1.27  tff(c_18, plain, (![D_12]: (r2_hidden(D_12, '#skF_3') | ~r2_hidden(D_12, '#skF_4') | ~m1_subset_1(D_12, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.27  tff(c_33, plain, (![B_16, C_17]: (r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), B_16, C_17), '#skF_3') | ~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), B_16, C_17), '#skF_4') | C_17=B_16 | ~m1_subset_1(C_17, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_23, c_18])).
% 1.79/1.27  tff(c_4, plain, (![A_1, B_2, C_6]: (~r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | ~r2_hidden('#skF_1'(A_1, B_2, C_6), B_2) | C_6=B_2 | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.79/1.27  tff(c_118, plain, (~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | '#skF_3'='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_97, c_4])).
% 1.79/1.27  tff(c_121, plain, (~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_118])).
% 1.79/1.27  tff(c_122, plain, (~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_12, c_121])).
% 1.79/1.27  tff(c_126, plain, (~r2_hidden('#skF_1'(k1_zfmisc_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_33, c_122])).
% 1.79/1.27  tff(c_132, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_97, c_126])).
% 1.79/1.27  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_132])).
% 1.79/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.27  
% 1.79/1.27  Inference rules
% 1.79/1.27  ----------------------
% 1.79/1.27  #Ref     : 0
% 1.79/1.27  #Sup     : 12
% 1.79/1.27  #Fact    : 4
% 1.79/1.27  #Define  : 0
% 1.79/1.27  #Split   : 0
% 1.79/1.27  #Chain   : 0
% 1.79/1.27  #Close   : 0
% 1.79/1.27  
% 1.79/1.27  Ordering : KBO
% 1.79/1.27  
% 1.79/1.27  Simplification rules
% 1.79/1.27  ----------------------
% 1.79/1.27  #Subsume      : 0
% 1.79/1.27  #Demod        : 13
% 1.79/1.27  #Tautology    : 8
% 1.79/1.27  #SimpNegUnit  : 4
% 1.79/1.27  #BackRed      : 0
% 1.79/1.27  
% 1.79/1.27  #Partial instantiations: 0
% 1.79/1.27  #Strategies tried      : 1
% 1.79/1.27  
% 1.79/1.27  Timing (in seconds)
% 1.79/1.27  ----------------------
% 1.79/1.27  Preprocessing        : 0.26
% 1.79/1.27  Parsing              : 0.14
% 1.79/1.28  CNF conversion       : 0.02
% 1.79/1.28  Main loop            : 0.14
% 1.79/1.28  Inferencing          : 0.06
% 1.79/1.28  Reduction            : 0.04
% 1.79/1.28  Demodulation         : 0.03
% 1.79/1.28  BG Simplification    : 0.01
% 1.79/1.28  Subsumption          : 0.03
% 1.79/1.28  Abstraction          : 0.01
% 1.79/1.28  MUC search           : 0.00
% 1.79/1.28  Cooper               : 0.00
% 1.79/1.28  Total                : 0.43
% 1.79/1.28  Index Insertion      : 0.00
% 1.79/1.28  Index Deletion       : 0.00
% 1.79/1.28  Index Matching       : 0.00
% 1.79/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
