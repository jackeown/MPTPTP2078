%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:44 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   42 (  74 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 181 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_51,plain,(
    ! [A_32,C_33,B_34] :
      ( m1_subset_1(A_32,C_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    ! [A_35] :
      ( m1_subset_1(A_35,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_35,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_26,plain,(
    ! [D_20] :
      ( r2_hidden(D_20,'#skF_4')
      | ~ r2_hidden(D_20,'#skF_5')
      | ~ m1_subset_1(D_20,k1_zfmisc_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_70,plain,(
    ! [A_36] :
      ( r2_hidden(A_36,'#skF_4')
      | ~ r2_hidden(A_36,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_26])).

tff(c_100,plain,(
    ! [A_42] :
      ( r2_hidden('#skF_1'(A_42,'#skF_5'),'#skF_4')
      | ~ r2_xboole_0(A_42,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),A_3)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_8])).

tff(c_108,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_105])).

tff(c_111,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_108])).

tff(c_168,plain,(
    ! [A_57,B_58,C_59] :
      ( r2_hidden('#skF_2'(A_57,B_58,C_59),B_58)
      | r1_tarski(B_58,C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    ! [A_37] :
      ( m1_subset_1(A_37,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_37,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_51])).

tff(c_28,plain,(
    ! [D_20] :
      ( r2_hidden(D_20,'#skF_5')
      | ~ r2_hidden(D_20,'#skF_4')
      | ~ m1_subset_1(D_20,k1_zfmisc_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_83,plain,(
    ! [A_37] :
      ( r2_hidden(A_37,'#skF_5')
      | ~ r2_hidden(A_37,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_28])).

tff(c_94,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r2_hidden('#skF_2'(A_39,B_40,C_41),C_41)
      | r1_tarski(B_40,C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_99,plain,(
    ! [B_40,A_39] :
      ( r1_tarski(B_40,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39))
      | ~ r2_hidden('#skF_2'(A_39,B_40,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_83,c_94])).

tff(c_172,plain,(
    ! [A_57] :
      ( r1_tarski('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_57))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_168,c_99])).

tff(c_233,plain,(
    ! [A_64] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_64))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_64)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_111,c_172])).

tff(c_244,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_22,c_233])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:29:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.25  
% 2.32/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.25  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.32/1.25  
% 2.32/1.25  %Foreground sorts:
% 2.32/1.25  
% 2.32/1.25  
% 2.32/1.25  %Background operators:
% 2.32/1.25  
% 2.32/1.25  
% 2.32/1.25  %Foreground operators:
% 2.32/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.32/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.32/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.32/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.32/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.32/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.32/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.32/1.25  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.32/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.32/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.32/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.32/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.32/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.32/1.25  
% 2.43/1.26  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 2.43/1.26  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.43/1.26  tff(f_42, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.43/1.26  tff(f_62, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.43/1.26  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 2.43/1.26  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.43/1.26  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.43/1.26  tff(c_20, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.43/1.26  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.43/1.26  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.43/1.26  tff(c_51, plain, (![A_32, C_33, B_34]: (m1_subset_1(A_32, C_33) | ~m1_subset_1(B_34, k1_zfmisc_1(C_33)) | ~r2_hidden(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.43/1.26  tff(c_58, plain, (![A_35]: (m1_subset_1(A_35, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_35, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_51])).
% 2.43/1.26  tff(c_26, plain, (![D_20]: (r2_hidden(D_20, '#skF_4') | ~r2_hidden(D_20, '#skF_5') | ~m1_subset_1(D_20, k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.43/1.26  tff(c_70, plain, (![A_36]: (r2_hidden(A_36, '#skF_4') | ~r2_hidden(A_36, '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_26])).
% 2.43/1.26  tff(c_100, plain, (![A_42]: (r2_hidden('#skF_1'(A_42, '#skF_5'), '#skF_4') | ~r2_xboole_0(A_42, '#skF_5'))), inference(resolution, [status(thm)], [c_10, c_70])).
% 2.43/1.26  tff(c_8, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), A_3) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.43/1.26  tff(c_105, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_100, c_8])).
% 2.43/1.26  tff(c_108, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_2, c_105])).
% 2.43/1.26  tff(c_111, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_20, c_108])).
% 2.43/1.26  tff(c_168, plain, (![A_57, B_58, C_59]: (r2_hidden('#skF_2'(A_57, B_58, C_59), B_58) | r1_tarski(B_58, C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.43/1.26  tff(c_76, plain, (![A_37]: (m1_subset_1(A_37, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_37, '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_51])).
% 2.43/1.26  tff(c_28, plain, (![D_20]: (r2_hidden(D_20, '#skF_5') | ~r2_hidden(D_20, '#skF_4') | ~m1_subset_1(D_20, k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.43/1.26  tff(c_83, plain, (![A_37]: (r2_hidden(A_37, '#skF_5') | ~r2_hidden(A_37, '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_28])).
% 2.43/1.26  tff(c_94, plain, (![A_39, B_40, C_41]: (~r2_hidden('#skF_2'(A_39, B_40, C_41), C_41) | r1_tarski(B_40, C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(A_39)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.43/1.26  tff(c_99, plain, (![B_40, A_39]: (r1_tarski(B_40, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_39)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)) | ~r2_hidden('#skF_2'(A_39, B_40, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_83, c_94])).
% 2.43/1.26  tff(c_172, plain, (![A_57]: (r1_tarski('#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_57)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_168, c_99])).
% 2.43/1.26  tff(c_233, plain, (![A_64]: (~m1_subset_1('#skF_5', k1_zfmisc_1(A_64)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_64)))), inference(negUnitSimplification, [status(thm)], [c_111, c_111, c_172])).
% 2.43/1.26  tff(c_244, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_22, c_233])).
% 2.43/1.26  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_244])).
% 2.43/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.26  
% 2.43/1.26  Inference rules
% 2.43/1.26  ----------------------
% 2.43/1.26  #Ref     : 0
% 2.43/1.26  #Sup     : 47
% 2.43/1.26  #Fact    : 0
% 2.43/1.26  #Define  : 0
% 2.43/1.26  #Split   : 3
% 2.43/1.26  #Chain   : 0
% 2.43/1.26  #Close   : 0
% 2.43/1.26  
% 2.43/1.26  Ordering : KBO
% 2.43/1.26  
% 2.43/1.26  Simplification rules
% 2.43/1.26  ----------------------
% 2.43/1.26  #Subsume      : 8
% 2.43/1.26  #Demod        : 1
% 2.43/1.26  #Tautology    : 4
% 2.43/1.26  #SimpNegUnit  : 3
% 2.43/1.26  #BackRed      : 0
% 2.43/1.26  
% 2.43/1.26  #Partial instantiations: 0
% 2.43/1.26  #Strategies tried      : 1
% 2.43/1.26  
% 2.43/1.26  Timing (in seconds)
% 2.43/1.26  ----------------------
% 2.43/1.26  Preprocessing        : 0.28
% 2.43/1.26  Parsing              : 0.15
% 2.43/1.26  CNF conversion       : 0.02
% 2.43/1.27  Main loop            : 0.21
% 2.43/1.27  Inferencing          : 0.08
% 2.43/1.27  Reduction            : 0.05
% 2.43/1.27  Demodulation         : 0.03
% 2.43/1.27  BG Simplification    : 0.01
% 2.43/1.27  Subsumption          : 0.06
% 2.43/1.27  Abstraction          : 0.01
% 2.43/1.27  MUC search           : 0.00
% 2.43/1.27  Cooper               : 0.00
% 2.43/1.27  Total                : 0.52
% 2.43/1.27  Index Insertion      : 0.00
% 2.43/1.27  Index Deletion       : 0.00
% 2.43/1.27  Index Matching       : 0.00
% 2.43/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
