%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:44 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 177 expanded)
%              Number of leaves         :   19 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  118 ( 419 expanded)
%              Number of equality atoms :    8 (  23 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_24,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_36])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_235,plain,(
    ! [A_64,B_65,B_66] :
      ( r2_hidden('#skF_1'(A_64,B_65),B_66)
      | ~ r1_tarski(A_64,B_66)
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_279,plain,(
    ! [A_70,B_71,B_72] :
      ( m1_subset_1('#skF_1'(A_70,B_71),B_72)
      | ~ r1_tarski(A_70,B_72)
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_235,c_18])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_294,plain,(
    ! [A_70,B_71,B_14] :
      ( r1_tarski('#skF_1'(A_70,B_71),B_14)
      | ~ r1_tarski(A_70,k1_zfmisc_1(B_14))
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_279,c_20])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    ! [D_19] :
      ( r2_hidden(D_19,'#skF_5')
      | ~ r2_hidden(D_19,'#skF_4')
      | ~ m1_subset_1(D_19,k1_zfmisc_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_146,plain,(
    ! [A_50] :
      ( r2_hidden(A_50,'#skF_5')
      | ~ r2_hidden(A_50,'#skF_4')
      | ~ r1_tarski(A_50,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_330,plain,(
    ! [A_82] :
      ( r1_tarski(A_82,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_82,'#skF_5'),'#skF_4')
      | ~ r1_tarski('#skF_1'(A_82,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_340,plain,
    ( ~ r1_tarski('#skF_1'('#skF_4','#skF_5'),'#skF_3')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_330])).

tff(c_341,plain,(
    ~ r1_tarski('#skF_1'('#skF_4','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_344,plain,
    ( ~ r1_tarski('#skF_4',k1_zfmisc_1('#skF_3'))
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_294,c_341])).

tff(c_347,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_344])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_112,plain,(
    ! [D_45] :
      ( r2_hidden(D_45,'#skF_4')
      | ~ r2_hidden(D_45,'#skF_5')
      | ~ m1_subset_1(D_45,k1_zfmisc_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_135,plain,(
    ! [A_49] :
      ( r2_hidden(A_49,'#skF_4')
      | ~ r2_hidden(A_49,'#skF_5')
      | ~ r1_tarski(A_49,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_112])).

tff(c_430,plain,(
    ! [A_85] :
      ( r2_hidden('#skF_2'(A_85,'#skF_5'),'#skF_4')
      | ~ r1_tarski('#skF_2'(A_85,'#skF_5'),'#skF_3')
      | ~ r2_xboole_0(A_85,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_135])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),A_8)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_453,plain,
    ( ~ r1_tarski('#skF_2'('#skF_4','#skF_5'),'#skF_3')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_430,c_14])).

tff(c_455,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_453])).

tff(c_458,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_455])).

tff(c_461,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_458])).

tff(c_463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_461])).

tff(c_465,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_453])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_43,plain,(
    r1_tarski('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_36])).

tff(c_180,plain,(
    ! [A_54,B_55,B_56] :
      ( r2_hidden('#skF_2'(A_54,B_55),B_56)
      | ~ r1_tarski(B_55,B_56)
      | ~ r2_xboole_0(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_16,c_128])).

tff(c_263,plain,(
    ! [A_67,B_68,B_69] :
      ( m1_subset_1('#skF_2'(A_67,B_68),B_69)
      | ~ r1_tarski(B_68,B_69)
      | ~ r2_xboole_0(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_180,c_18])).

tff(c_278,plain,(
    ! [A_67,B_68,B_14] :
      ( r1_tarski('#skF_2'(A_67,B_68),B_14)
      | ~ r1_tarski(B_68,k1_zfmisc_1(B_14))
      | ~ r2_xboole_0(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_263,c_20])).

tff(c_464,plain,(
    ~ r1_tarski('#skF_2'('#skF_4','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_453])).

tff(c_500,plain,
    ( ~ r1_tarski('#skF_5',k1_zfmisc_1('#skF_3'))
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_278,c_464])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_43,c_500])).

tff(c_505,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_593,plain,(
    ! [A_89] :
      ( r2_hidden('#skF_2'(A_89,'#skF_5'),'#skF_4')
      | ~ r1_tarski('#skF_2'(A_89,'#skF_5'),'#skF_3')
      | ~ r2_xboole_0(A_89,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_135])).

tff(c_616,plain,
    ( ~ r1_tarski('#skF_2'('#skF_4','#skF_5'),'#skF_3')
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_593,c_14])).

tff(c_618,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_616])).

tff(c_621,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_618])).

tff(c_624,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_621])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_624])).

tff(c_628,plain,(
    r2_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_616])).

tff(c_627,plain,(
    ~ r1_tarski('#skF_2'('#skF_4','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_616])).

tff(c_663,plain,
    ( ~ r1_tarski('#skF_5',k1_zfmisc_1('#skF_3'))
    | ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_278,c_627])).

tff(c_667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_43,c_663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:08:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.41  
% 2.84/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.41  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.84/1.41  
% 2.84/1.41  %Foreground sorts:
% 2.84/1.41  
% 2.84/1.41  
% 2.84/1.41  %Background operators:
% 2.84/1.41  
% 2.84/1.41  
% 2.84/1.41  %Foreground operators:
% 2.84/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.84/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.84/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.84/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.84/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.41  
% 2.84/1.43  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 2.84/1.43  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.84/1.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.84/1.43  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.84/1.43  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.84/1.43  tff(f_49, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.84/1.43  tff(c_24, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.43  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.43  tff(c_36, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.43  tff(c_44, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_36])).
% 2.84/1.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.84/1.43  tff(c_128, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.84/1.43  tff(c_235, plain, (![A_64, B_65, B_66]: (r2_hidden('#skF_1'(A_64, B_65), B_66) | ~r1_tarski(A_64, B_66) | r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_6, c_128])).
% 2.84/1.43  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.84/1.43  tff(c_279, plain, (![A_70, B_71, B_72]: (m1_subset_1('#skF_1'(A_70, B_71), B_72) | ~r1_tarski(A_70, B_72) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_235, c_18])).
% 2.84/1.43  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.43  tff(c_294, plain, (![A_70, B_71, B_14]: (r1_tarski('#skF_1'(A_70, B_71), B_14) | ~r1_tarski(A_70, k1_zfmisc_1(B_14)) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_279, c_20])).
% 2.84/1.43  tff(c_46, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.43  tff(c_32, plain, (![D_19]: (r2_hidden(D_19, '#skF_5') | ~r2_hidden(D_19, '#skF_4') | ~m1_subset_1(D_19, k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.43  tff(c_146, plain, (![A_50]: (r2_hidden(A_50, '#skF_5') | ~r2_hidden(A_50, '#skF_4') | ~r1_tarski(A_50, '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_32])).
% 2.84/1.43  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.84/1.43  tff(c_330, plain, (![A_82]: (r1_tarski(A_82, '#skF_5') | ~r2_hidden('#skF_1'(A_82, '#skF_5'), '#skF_4') | ~r1_tarski('#skF_1'(A_82, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_146, c_4])).
% 2.84/1.43  tff(c_340, plain, (~r1_tarski('#skF_1'('#skF_4', '#skF_5'), '#skF_3') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_330])).
% 2.84/1.43  tff(c_341, plain, (~r1_tarski('#skF_1'('#skF_4', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_340])).
% 2.84/1.43  tff(c_344, plain, (~r1_tarski('#skF_4', k1_zfmisc_1('#skF_3')) | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_294, c_341])).
% 2.84/1.43  tff(c_347, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_344])).
% 2.84/1.43  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.84/1.43  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.84/1.43  tff(c_22, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.43  tff(c_112, plain, (![D_45]: (r2_hidden(D_45, '#skF_4') | ~r2_hidden(D_45, '#skF_5') | ~m1_subset_1(D_45, k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.43  tff(c_135, plain, (![A_49]: (r2_hidden(A_49, '#skF_4') | ~r2_hidden(A_49, '#skF_5') | ~r1_tarski(A_49, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_112])).
% 2.84/1.43  tff(c_430, plain, (![A_85]: (r2_hidden('#skF_2'(A_85, '#skF_5'), '#skF_4') | ~r1_tarski('#skF_2'(A_85, '#skF_5'), '#skF_3') | ~r2_xboole_0(A_85, '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_135])).
% 2.84/1.43  tff(c_14, plain, (![A_8, B_9]: (~r2_hidden('#skF_2'(A_8, B_9), A_8) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.84/1.43  tff(c_453, plain, (~r1_tarski('#skF_2'('#skF_4', '#skF_5'), '#skF_3') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_430, c_14])).
% 2.84/1.43  tff(c_455, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_453])).
% 2.84/1.43  tff(c_458, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_455])).
% 2.84/1.43  tff(c_461, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_458])).
% 2.84/1.43  tff(c_463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_461])).
% 2.84/1.43  tff(c_465, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_453])).
% 2.84/1.43  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.43  tff(c_43, plain, (r1_tarski('#skF_5', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_36])).
% 2.84/1.43  tff(c_180, plain, (![A_54, B_55, B_56]: (r2_hidden('#skF_2'(A_54, B_55), B_56) | ~r1_tarski(B_55, B_56) | ~r2_xboole_0(A_54, B_55))), inference(resolution, [status(thm)], [c_16, c_128])).
% 2.84/1.43  tff(c_263, plain, (![A_67, B_68, B_69]: (m1_subset_1('#skF_2'(A_67, B_68), B_69) | ~r1_tarski(B_68, B_69) | ~r2_xboole_0(A_67, B_68))), inference(resolution, [status(thm)], [c_180, c_18])).
% 2.84/1.43  tff(c_278, plain, (![A_67, B_68, B_14]: (r1_tarski('#skF_2'(A_67, B_68), B_14) | ~r1_tarski(B_68, k1_zfmisc_1(B_14)) | ~r2_xboole_0(A_67, B_68))), inference(resolution, [status(thm)], [c_263, c_20])).
% 2.84/1.43  tff(c_464, plain, (~r1_tarski('#skF_2'('#skF_4', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_453])).
% 2.84/1.43  tff(c_500, plain, (~r1_tarski('#skF_5', k1_zfmisc_1('#skF_3')) | ~r2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_278, c_464])).
% 2.84/1.43  tff(c_504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_465, c_43, c_500])).
% 2.84/1.43  tff(c_505, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_340])).
% 2.84/1.43  tff(c_593, plain, (![A_89]: (r2_hidden('#skF_2'(A_89, '#skF_5'), '#skF_4') | ~r1_tarski('#skF_2'(A_89, '#skF_5'), '#skF_3') | ~r2_xboole_0(A_89, '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_135])).
% 2.84/1.43  tff(c_616, plain, (~r1_tarski('#skF_2'('#skF_4', '#skF_5'), '#skF_3') | ~r2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_593, c_14])).
% 2.84/1.43  tff(c_618, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_616])).
% 2.84/1.43  tff(c_621, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_618])).
% 2.84/1.43  tff(c_624, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_621])).
% 2.84/1.43  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_624])).
% 2.84/1.43  tff(c_628, plain, (r2_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_616])).
% 2.84/1.43  tff(c_627, plain, (~r1_tarski('#skF_2'('#skF_4', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_616])).
% 2.84/1.43  tff(c_663, plain, (~r1_tarski('#skF_5', k1_zfmisc_1('#skF_3')) | ~r2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_278, c_627])).
% 2.84/1.43  tff(c_667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_628, c_43, c_663])).
% 2.84/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.43  
% 2.84/1.43  Inference rules
% 2.84/1.43  ----------------------
% 2.84/1.43  #Ref     : 0
% 2.84/1.43  #Sup     : 120
% 2.84/1.43  #Fact    : 0
% 2.84/1.43  #Define  : 0
% 2.84/1.43  #Split   : 10
% 2.84/1.43  #Chain   : 0
% 2.84/1.43  #Close   : 0
% 2.84/1.43  
% 2.84/1.43  Ordering : KBO
% 2.84/1.43  
% 2.84/1.43  Simplification rules
% 2.84/1.43  ----------------------
% 2.84/1.43  #Subsume      : 21
% 2.84/1.43  #Demod        : 54
% 2.84/1.43  #Tautology    : 20
% 2.84/1.43  #SimpNegUnit  : 8
% 2.84/1.43  #BackRed      : 24
% 2.84/1.43  
% 2.84/1.43  #Partial instantiations: 0
% 2.84/1.43  #Strategies tried      : 1
% 2.84/1.43  
% 2.84/1.43  Timing (in seconds)
% 2.84/1.43  ----------------------
% 2.84/1.43  Preprocessing        : 0.28
% 2.84/1.43  Parsing              : 0.15
% 2.84/1.43  CNF conversion       : 0.02
% 2.84/1.43  Main loop            : 0.38
% 2.84/1.43  Inferencing          : 0.14
% 2.84/1.43  Reduction            : 0.10
% 2.84/1.43  Demodulation         : 0.07
% 2.84/1.43  BG Simplification    : 0.02
% 2.84/1.43  Subsumption          : 0.10
% 2.84/1.43  Abstraction          : 0.02
% 2.84/1.43  MUC search           : 0.00
% 2.84/1.43  Cooper               : 0.00
% 2.84/1.43  Total                : 0.70
% 2.84/1.43  Index Insertion      : 0.00
% 2.84/1.43  Index Deletion       : 0.00
% 2.84/1.43  Index Matching       : 0.00
% 2.84/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
