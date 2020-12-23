%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:48 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 110 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_68,axiom,(
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

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_79,plain,(
    ! [B_35,A_36] :
      ( m1_subset_1(B_35,A_36)
      | ~ r2_hidden(B_35,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ! [C_7,A_3] :
      ( m1_subset_1(C_7,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_92,plain,(
    ! [C_7,A_3] :
      ( m1_subset_1(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_85])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    ! [A_11,B_12,C_16] :
      ( m1_subset_1('#skF_3'(A_11,B_12,C_16),A_11)
      | r1_tarski(B_12,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,'#skF_5')
      | ~ m1_subset_1(C_19,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_212,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r2_hidden('#skF_3'(A_63,B_64,C_65),C_65)
      | r1_tarski(B_64,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_280,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(B_75,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_76))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ m1_subset_1('#skF_3'(A_76,B_75,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_212])).

tff(c_284,plain,(
    ! [B_12] :
      ( r1_tarski(B_12,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(B_12,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_34,c_280])).

tff(c_292,plain,(
    ! [B_77] :
      ( r1_tarski(B_77,'#skF_5')
      | ~ m1_subset_1(B_77,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_284])).

tff(c_327,plain,(
    ! [C_78] :
      ( r1_tarski(C_78,'#skF_5')
      | ~ r1_tarski(C_78,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92,c_292])).

tff(c_36,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_61,plain,(
    ! [B_31,A_32] :
      ( r2_hidden(B_31,A_32)
      | ~ m1_subset_1(B_31,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_65,plain,(
    ! [B_31,A_3] :
      ( r1_tarski(B_31,A_3)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_61,c_8])).

tff(c_69,plain,(
    ! [B_33,A_34] :
      ( r1_tarski(B_33,A_34)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_65])).

tff(c_78,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_69])).

tff(c_103,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_103])).

tff(c_110,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_105])).

tff(c_344,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_327,c_110])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_344])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.29  
% 2.14/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.14/1.29  
% 2.14/1.29  %Foreground sorts:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Background operators:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Foreground operators:
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.29  
% 2.14/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.14/1.30  tff(f_54, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.14/1.30  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.14/1.30  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.14/1.30  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 2.14/1.30  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 2.14/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.30  tff(c_28, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.30  tff(c_10, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.14/1.30  tff(c_79, plain, (![B_35, A_36]: (m1_subset_1(B_35, A_36) | ~r2_hidden(B_35, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.30  tff(c_85, plain, (![C_7, A_3]: (m1_subset_1(C_7, k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(resolution, [status(thm)], [c_10, c_79])).
% 2.14/1.30  tff(c_92, plain, (![C_7, A_3]: (m1_subset_1(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(negUnitSimplification, [status(thm)], [c_28, c_85])).
% 2.14/1.30  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.14/1.30  tff(c_34, plain, (![A_11, B_12, C_16]: (m1_subset_1('#skF_3'(A_11, B_12, C_16), A_11) | r1_tarski(B_12, C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.14/1.30  tff(c_38, plain, (![C_19]: (r2_hidden(C_19, '#skF_5') | ~m1_subset_1(C_19, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.14/1.30  tff(c_212, plain, (![A_63, B_64, C_65]: (~r2_hidden('#skF_3'(A_63, B_64, C_65), C_65) | r1_tarski(B_64, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.14/1.30  tff(c_280, plain, (![B_75, A_76]: (r1_tarski(B_75, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_76)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~m1_subset_1('#skF_3'(A_76, B_75, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_212])).
% 2.14/1.30  tff(c_284, plain, (![B_12]: (r1_tarski(B_12, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~m1_subset_1(B_12, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_34, c_280])).
% 2.14/1.30  tff(c_292, plain, (![B_77]: (r1_tarski(B_77, '#skF_5') | ~m1_subset_1(B_77, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_284])).
% 2.14/1.30  tff(c_327, plain, (![C_78]: (r1_tarski(C_78, '#skF_5') | ~r1_tarski(C_78, '#skF_4'))), inference(resolution, [status(thm)], [c_92, c_292])).
% 2.14/1.30  tff(c_36, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.14/1.30  tff(c_61, plain, (![B_31, A_32]: (r2_hidden(B_31, A_32) | ~m1_subset_1(B_31, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.30  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.14/1.30  tff(c_65, plain, (![B_31, A_3]: (r1_tarski(B_31, A_3) | ~m1_subset_1(B_31, k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_61, c_8])).
% 2.14/1.30  tff(c_69, plain, (![B_33, A_34]: (r1_tarski(B_33, A_34) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)))), inference(negUnitSimplification, [status(thm)], [c_28, c_65])).
% 2.14/1.30  tff(c_78, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_69])).
% 2.14/1.30  tff(c_103, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.30  tff(c_105, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_103])).
% 2.14/1.30  tff(c_110, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_105])).
% 2.14/1.30  tff(c_344, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_327, c_110])).
% 2.14/1.30  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_344])).
% 2.14/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  Inference rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Ref     : 0
% 2.14/1.30  #Sup     : 58
% 2.14/1.30  #Fact    : 0
% 2.14/1.30  #Define  : 0
% 2.14/1.30  #Split   : 1
% 2.14/1.31  #Chain   : 0
% 2.14/1.31  #Close   : 0
% 2.14/1.31  
% 2.14/1.31  Ordering : KBO
% 2.14/1.31  
% 2.14/1.31  Simplification rules
% 2.14/1.31  ----------------------
% 2.14/1.31  #Subsume      : 6
% 2.14/1.31  #Demod        : 7
% 2.14/1.31  #Tautology    : 13
% 2.14/1.31  #SimpNegUnit  : 10
% 2.14/1.31  #BackRed      : 0
% 2.14/1.31  
% 2.14/1.31  #Partial instantiations: 0
% 2.14/1.31  #Strategies tried      : 1
% 2.14/1.31  
% 2.14/1.31  Timing (in seconds)
% 2.14/1.31  ----------------------
% 2.14/1.31  Preprocessing        : 0.30
% 2.14/1.31  Parsing              : 0.16
% 2.14/1.31  CNF conversion       : 0.02
% 2.14/1.31  Main loop            : 0.25
% 2.14/1.31  Inferencing          : 0.09
% 2.14/1.31  Reduction            : 0.06
% 2.14/1.31  Demodulation         : 0.04
% 2.14/1.31  BG Simplification    : 0.02
% 2.14/1.31  Subsumption          : 0.06
% 2.14/1.31  Abstraction          : 0.01
% 2.14/1.31  MUC search           : 0.00
% 2.14/1.31  Cooper               : 0.00
% 2.14/1.31  Total                : 0.58
% 2.14/1.31  Index Insertion      : 0.00
% 2.14/1.31  Index Deletion       : 0.00
% 2.14/1.31  Index Matching       : 0.00
% 2.14/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
