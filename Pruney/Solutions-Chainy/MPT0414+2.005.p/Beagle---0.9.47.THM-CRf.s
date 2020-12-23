%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:43 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 235 expanded)
%              Number of leaves         :   16 (  85 expanded)
%              Depth                    :   13
%              Number of atoms          :   96 ( 569 expanded)
%              Number of equality atoms :    6 (  43 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_20,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_33])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [C_31,B_32,A_33] :
      ( r2_hidden(C_31,B_32)
      | ~ r2_hidden(C_31,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_138,plain,(
    ! [A_42,B_43,B_44] :
      ( r2_hidden('#skF_1'(A_42,B_43),B_44)
      | ~ r1_tarski(A_42,B_44)
      | r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_161,plain,(
    ! [A_45,B_46,B_47] :
      ( m1_subset_1('#skF_1'(A_45,B_46),B_47)
      | ~ r1_tarski(A_45,B_47)
      | r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_138,c_14])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_176,plain,(
    ! [A_45,B_46,B_11] :
      ( r1_tarski('#skF_1'(A_45,B_46),B_11)
      | ~ r1_tarski(A_45,k1_zfmisc_1(B_11))
      | r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_161,c_16])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    ! [D_24] :
      ( r2_hidden(D_24,'#skF_3')
      | ~ r2_hidden(D_24,'#skF_4')
      | ~ m1_subset_1(D_24,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_105,plain,(
    ! [A_37] :
      ( r2_hidden(A_37,'#skF_3')
      | ~ r2_hidden(A_37,'#skF_4')
      | ~ r1_tarski(A_37,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_46])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_190,plain,(
    ! [A_53] :
      ( r1_tarski(A_53,'#skF_3')
      | ~ r2_hidden('#skF_1'(A_53,'#skF_3'),'#skF_4')
      | ~ r1_tarski('#skF_1'(A_53,'#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_105,c_4])).

tff(c_200,plain,
    ( ~ r1_tarski('#skF_1'('#skF_4','#skF_3'),'#skF_2')
    | r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_190])).

tff(c_225,plain,(
    ~ r1_tarski('#skF_1'('#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_228,plain,
    ( ~ r1_tarski('#skF_4',k1_zfmisc_1('#skF_2'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_225])).

tff(c_231,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_228])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_233,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_231,c_8])).

tff(c_236,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_233])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_45,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_33])).

tff(c_94,plain,(
    ! [D_36] :
      ( r2_hidden(D_36,'#skF_4')
      | ~ r2_hidden(D_36,'#skF_3')
      | ~ m1_subset_1(D_36,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_118,plain,(
    ! [A_38] :
      ( r2_hidden(A_38,'#skF_4')
      | ~ r2_hidden(A_38,'#skF_3')
      | ~ r1_tarski(A_38,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_94])).

tff(c_237,plain,(
    ! [B_55] :
      ( r2_hidden('#skF_1'('#skF_3',B_55),'#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3',B_55),'#skF_2')
      | r1_tarski('#skF_3',B_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_252,plain,
    ( ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_237,c_4])).

tff(c_263,plain,(
    ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_236,c_252])).

tff(c_267,plain,
    ( ~ r1_tarski('#skF_3',k1_zfmisc_1('#skF_2'))
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_176,c_263])).

tff(c_270,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_267])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_270])).

tff(c_273,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_276,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_273,c_8])).

tff(c_279,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_276])).

tff(c_344,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'('#skF_3',B_59),'#skF_4')
      | ~ r1_tarski('#skF_1'('#skF_3',B_59),'#skF_2')
      | r1_tarski('#skF_3',B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_359,plain,
    ( ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_2')
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_344,c_4])).

tff(c_370,plain,(
    ~ r1_tarski('#skF_1'('#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_279,c_359])).

tff(c_374,plain,
    ( ~ r1_tarski('#skF_3',k1_zfmisc_1('#skF_2'))
    | r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_176,c_370])).

tff(c_377,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_374])).

tff(c_379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_377])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.28  %$ r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.14/1.28  
% 2.14/1.28  %Foreground sorts:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Background operators:
% 2.14/1.28  
% 2.14/1.28  
% 2.14/1.28  %Foreground operators:
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.28  
% 2.14/1.30  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 2.14/1.30  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.14/1.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.14/1.30  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.14/1.30  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.14/1.30  tff(c_20, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.30  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.30  tff(c_33, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.30  tff(c_44, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_33])).
% 2.14/1.30  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.30  tff(c_78, plain, (![C_31, B_32, A_33]: (r2_hidden(C_31, B_32) | ~r2_hidden(C_31, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.30  tff(c_138, plain, (![A_42, B_43, B_44]: (r2_hidden('#skF_1'(A_42, B_43), B_44) | ~r1_tarski(A_42, B_44) | r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_6, c_78])).
% 2.14/1.30  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.14/1.30  tff(c_161, plain, (![A_45, B_46, B_47]: (m1_subset_1('#skF_1'(A_45, B_46), B_47) | ~r1_tarski(A_45, B_47) | r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_138, c_14])).
% 2.14/1.30  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.30  tff(c_176, plain, (![A_45, B_46, B_11]: (r1_tarski('#skF_1'(A_45, B_46), B_11) | ~r1_tarski(A_45, k1_zfmisc_1(B_11)) | r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_161, c_16])).
% 2.14/1.30  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.14/1.30  tff(c_46, plain, (![D_24]: (r2_hidden(D_24, '#skF_3') | ~r2_hidden(D_24, '#skF_4') | ~m1_subset_1(D_24, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.30  tff(c_105, plain, (![A_37]: (r2_hidden(A_37, '#skF_3') | ~r2_hidden(A_37, '#skF_4') | ~r1_tarski(A_37, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_46])).
% 2.14/1.30  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.30  tff(c_190, plain, (![A_53]: (r1_tarski(A_53, '#skF_3') | ~r2_hidden('#skF_1'(A_53, '#skF_3'), '#skF_4') | ~r1_tarski('#skF_1'(A_53, '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_105, c_4])).
% 2.14/1.30  tff(c_200, plain, (~r1_tarski('#skF_1'('#skF_4', '#skF_3'), '#skF_2') | r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_190])).
% 2.14/1.30  tff(c_225, plain, (~r1_tarski('#skF_1'('#skF_4', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_200])).
% 2.14/1.30  tff(c_228, plain, (~r1_tarski('#skF_4', k1_zfmisc_1('#skF_2')) | r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_176, c_225])).
% 2.14/1.30  tff(c_231, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_228])).
% 2.14/1.30  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.14/1.30  tff(c_233, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_231, c_8])).
% 2.14/1.30  tff(c_236, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_20, c_233])).
% 2.14/1.30  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.30  tff(c_45, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_33])).
% 2.14/1.30  tff(c_94, plain, (![D_36]: (r2_hidden(D_36, '#skF_4') | ~r2_hidden(D_36, '#skF_3') | ~m1_subset_1(D_36, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.30  tff(c_118, plain, (![A_38]: (r2_hidden(A_38, '#skF_4') | ~r2_hidden(A_38, '#skF_3') | ~r1_tarski(A_38, '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_94])).
% 2.14/1.30  tff(c_237, plain, (![B_55]: (r2_hidden('#skF_1'('#skF_3', B_55), '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', B_55), '#skF_2') | r1_tarski('#skF_3', B_55))), inference(resolution, [status(thm)], [c_6, c_118])).
% 2.14/1.30  tff(c_252, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_237, c_4])).
% 2.14/1.30  tff(c_263, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_236, c_236, c_252])).
% 2.14/1.30  tff(c_267, plain, (~r1_tarski('#skF_3', k1_zfmisc_1('#skF_2')) | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_176, c_263])).
% 2.14/1.30  tff(c_270, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_267])).
% 2.14/1.30  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_270])).
% 2.14/1.30  tff(c_273, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_200])).
% 2.14/1.30  tff(c_276, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_273, c_8])).
% 2.14/1.30  tff(c_279, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_20, c_276])).
% 2.14/1.30  tff(c_344, plain, (![B_59]: (r2_hidden('#skF_1'('#skF_3', B_59), '#skF_4') | ~r1_tarski('#skF_1'('#skF_3', B_59), '#skF_2') | r1_tarski('#skF_3', B_59))), inference(resolution, [status(thm)], [c_6, c_118])).
% 2.14/1.30  tff(c_359, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_2') | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_344, c_4])).
% 2.14/1.30  tff(c_370, plain, (~r1_tarski('#skF_1'('#skF_3', '#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_279, c_279, c_359])).
% 2.14/1.30  tff(c_374, plain, (~r1_tarski('#skF_3', k1_zfmisc_1('#skF_2')) | r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_176, c_370])).
% 2.14/1.30  tff(c_377, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_374])).
% 2.14/1.30  tff(c_379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279, c_377])).
% 2.14/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  Inference rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Ref     : 0
% 2.14/1.30  #Sup     : 68
% 2.14/1.30  #Fact    : 0
% 2.14/1.30  #Define  : 0
% 2.14/1.30  #Split   : 4
% 2.14/1.30  #Chain   : 0
% 2.14/1.30  #Close   : 0
% 2.14/1.30  
% 2.14/1.30  Ordering : KBO
% 2.14/1.30  
% 2.14/1.30  Simplification rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Subsume      : 9
% 2.14/1.30  #Demod        : 13
% 2.14/1.30  #Tautology    : 13
% 2.14/1.30  #SimpNegUnit  : 10
% 2.14/1.30  #BackRed      : 0
% 2.14/1.30  
% 2.14/1.30  #Partial instantiations: 0
% 2.14/1.30  #Strategies tried      : 1
% 2.14/1.30  
% 2.14/1.30  Timing (in seconds)
% 2.14/1.30  ----------------------
% 2.14/1.30  Preprocessing        : 0.28
% 2.14/1.30  Parsing              : 0.15
% 2.14/1.30  CNF conversion       : 0.02
% 2.14/1.30  Main loop            : 0.26
% 2.14/1.30  Inferencing          : 0.10
% 2.14/1.30  Reduction            : 0.07
% 2.14/1.30  Demodulation         : 0.05
% 2.14/1.30  BG Simplification    : 0.01
% 2.14/1.30  Subsumption          : 0.07
% 2.14/1.30  Abstraction          : 0.01
% 2.14/1.30  MUC search           : 0.00
% 2.14/1.30  Cooper               : 0.00
% 2.14/1.30  Total                : 0.58
% 2.14/1.30  Index Insertion      : 0.00
% 2.14/1.30  Index Deletion       : 0.00
% 2.14/1.30  Index Matching       : 0.00
% 2.14/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
