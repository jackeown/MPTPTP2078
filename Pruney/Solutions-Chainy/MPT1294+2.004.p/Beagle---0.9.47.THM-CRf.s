%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:38 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   42 (  72 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 ( 132 expanded)
%              Number of equality atoms :   29 (  88 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( ~ ( B != k1_xboole_0
              & k7_setfam_1(A,B) = k1_xboole_0 )
          & ~ ( k7_setfam_1(A,B) != k1_xboole_0
              & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(c_32,plain,
    ( k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_25,B_26] : ~ r2_hidden(A_25,k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_78,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_65])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_148,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_1'(A_51,B_52,C_53),C_53)
      | r2_hidden(k3_subset_1(A_51,'#skF_1'(A_51,B_52,C_53)),B_52)
      | k7_setfam_1(A_51,B_52) = C_53
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k1_zfmisc_1(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_162,plain,(
    ! [A_51,C_53] :
      ( r2_hidden('#skF_1'(A_51,'#skF_3',C_53),C_53)
      | k7_setfam_1(A_51,'#skF_3') = C_53
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k1_zfmisc_1(A_51)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(resolution,[status(thm)],[c_148,c_78])).

tff(c_169,plain,(
    ! [A_54,C_55] :
      ( r2_hidden('#skF_1'(A_54,'#skF_3',C_55),C_55)
      | k7_setfam_1(A_54,'#skF_3') = C_55
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_162])).

tff(c_175,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_1'(A_54,'#skF_3','#skF_3'),'#skF_3')
      | k7_setfam_1(A_54,'#skF_3') = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_72,c_169])).

tff(c_179,plain,(
    ! [A_54] : k7_setfam_1(A_54,'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_175])).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_3'
    | k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_81,plain,(
    k7_setfam_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_38])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_81])).

tff(c_185,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_184,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_216,plain,(
    ! [A_65,B_66] :
      ( k7_setfam_1(A_65,B_66) != k1_xboole_0
      | k1_xboole_0 = B_66
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_219,plain,
    ( k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_216])).

tff(c_226,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_219])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.25  
% 2.04/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.25  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.04/1.25  
% 2.04/1.25  %Foreground sorts:
% 2.04/1.25  
% 2.04/1.25  
% 2.04/1.25  %Background operators:
% 2.04/1.25  
% 2.04/1.25  
% 2.04/1.25  %Foreground operators:
% 2.04/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.25  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.04/1.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.04/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.25  
% 2.04/1.26  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tops_2)).
% 2.04/1.26  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.04/1.26  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.04/1.26  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.04/1.26  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.04/1.26  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.04/1.26  tff(c_32, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.04/1.26  tff(c_69, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_32])).
% 2.04/1.26  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.26  tff(c_62, plain, (![A_25, B_26]: (~r2_hidden(A_25, k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.04/1.26  tff(c_65, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 2.04/1.26  tff(c_78, plain, (![A_1]: (~r2_hidden(A_1, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_65])).
% 2.04/1.26  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.04/1.26  tff(c_72, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_10])).
% 2.04/1.26  tff(c_148, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_1'(A_51, B_52, C_53), C_53) | r2_hidden(k3_subset_1(A_51, '#skF_1'(A_51, B_52, C_53)), B_52) | k7_setfam_1(A_51, B_52)=C_53 | ~m1_subset_1(C_53, k1_zfmisc_1(k1_zfmisc_1(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.04/1.26  tff(c_162, plain, (![A_51, C_53]: (r2_hidden('#skF_1'(A_51, '#skF_3', C_53), C_53) | k7_setfam_1(A_51, '#skF_3')=C_53 | ~m1_subset_1(C_53, k1_zfmisc_1(k1_zfmisc_1(A_51))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(resolution, [status(thm)], [c_148, c_78])).
% 2.04/1.26  tff(c_169, plain, (![A_54, C_55]: (r2_hidden('#skF_1'(A_54, '#skF_3', C_55), C_55) | k7_setfam_1(A_54, '#skF_3')=C_55 | ~m1_subset_1(C_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_162])).
% 2.04/1.26  tff(c_175, plain, (![A_54]: (r2_hidden('#skF_1'(A_54, '#skF_3', '#skF_3'), '#skF_3') | k7_setfam_1(A_54, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_72, c_169])).
% 2.04/1.26  tff(c_179, plain, (![A_54]: (k7_setfam_1(A_54, '#skF_3')='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_78, c_175])).
% 2.04/1.26  tff(c_38, plain, (k1_xboole_0!='#skF_3' | k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.04/1.26  tff(c_81, plain, (k7_setfam_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_38])).
% 2.04/1.26  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_81])).
% 2.04/1.26  tff(c_185, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.04/1.26  tff(c_184, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.04/1.26  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.04/1.26  tff(c_216, plain, (![A_65, B_66]: (k7_setfam_1(A_65, B_66)!=k1_xboole_0 | k1_xboole_0=B_66 | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.04/1.26  tff(c_219, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_216])).
% 2.04/1.26  tff(c_226, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_219])).
% 2.04/1.26  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_226])).
% 2.04/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.26  
% 2.04/1.26  Inference rules
% 2.04/1.26  ----------------------
% 2.04/1.26  #Ref     : 0
% 2.04/1.26  #Sup     : 39
% 2.04/1.26  #Fact    : 0
% 2.04/1.26  #Define  : 0
% 2.04/1.26  #Split   : 1
% 2.04/1.26  #Chain   : 0
% 2.04/1.26  #Close   : 0
% 2.04/1.26  
% 2.04/1.26  Ordering : KBO
% 2.04/1.26  
% 2.04/1.26  Simplification rules
% 2.04/1.26  ----------------------
% 2.04/1.26  #Subsume      : 7
% 2.04/1.26  #Demod        : 21
% 2.04/1.26  #Tautology    : 26
% 2.04/1.26  #SimpNegUnit  : 2
% 2.04/1.26  #BackRed      : 5
% 2.04/1.26  
% 2.04/1.26  #Partial instantiations: 0
% 2.04/1.26  #Strategies tried      : 1
% 2.04/1.26  
% 2.04/1.26  Timing (in seconds)
% 2.04/1.26  ----------------------
% 2.04/1.26  Preprocessing        : 0.29
% 2.04/1.26  Parsing              : 0.15
% 2.04/1.26  CNF conversion       : 0.02
% 2.04/1.26  Main loop            : 0.16
% 2.04/1.26  Inferencing          : 0.06
% 2.04/1.26  Reduction            : 0.05
% 2.04/1.26  Demodulation         : 0.03
% 2.04/1.26  BG Simplification    : 0.01
% 2.04/1.26  Subsumption          : 0.03
% 2.04/1.26  Abstraction          : 0.01
% 2.04/1.26  MUC search           : 0.00
% 2.04/1.26  Cooper               : 0.00
% 2.04/1.26  Total                : 0.48
% 2.04/1.26  Index Insertion      : 0.00
% 2.04/1.26  Index Deletion       : 0.00
% 2.04/1.26  Index Matching       : 0.00
% 2.04/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
