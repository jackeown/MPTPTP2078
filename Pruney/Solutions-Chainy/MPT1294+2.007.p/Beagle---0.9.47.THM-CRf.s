%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:39 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   43 (  79 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 148 expanded)
%              Number of equality atoms :   29 ( 102 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

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

tff(c_47,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    ! [A_1] : k4_xboole_0('#skF_3',A_1) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_47,c_2])).

tff(c_65,plain,(
    ! [C_26,B_27] : ~ r2_hidden(C_26,k4_xboole_0(B_27,k1_tarski(C_26))) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    ! [C_26] : ~ r2_hidden(C_26,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_65])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_49,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_10])).

tff(c_124,plain,(
    ! [A_56,B_57,C_58] :
      ( r2_hidden('#skF_1'(A_56,B_57,C_58),C_58)
      | r2_hidden(k3_subset_1(A_56,'#skF_1'(A_56,B_57,C_58)),B_57)
      | k7_setfam_1(A_56,B_57) = C_58
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k1_zfmisc_1(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_144,plain,(
    ! [A_56,C_58] :
      ( r2_hidden('#skF_1'(A_56,'#skF_3',C_58),C_58)
      | k7_setfam_1(A_56,'#skF_3') = C_58
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k1_zfmisc_1(A_56)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(resolution,[status(thm)],[c_124,c_68])).

tff(c_158,plain,(
    ! [A_59,C_60] :
      ( r2_hidden('#skF_1'(A_59,'#skF_3',C_60),C_60)
      | k7_setfam_1(A_59,'#skF_3') = C_60
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_144])).

tff(c_164,plain,(
    ! [A_59] :
      ( r2_hidden('#skF_1'(A_59,'#skF_3','#skF_3'),'#skF_3')
      | k7_setfam_1(A_59,'#skF_3') = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_49,c_158])).

tff(c_168,plain,(
    ! [A_59] : k7_setfam_1(A_59,'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_164])).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_3'
    | k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_64,plain,(
    k7_setfam_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_47,c_38])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_64])).

tff(c_174,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_173,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_223,plain,(
    ! [A_76,B_77] :
      ( k7_setfam_1(A_76,B_77) != k1_xboole_0
      | k1_xboole_0 = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_226,plain,
    ( k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_223])).

tff(c_233,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_226])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:10:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.26  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.14/1.26  
% 2.14/1.26  %Foreground sorts:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Background operators:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Foreground operators:
% 2.14/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.26  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.14/1.26  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.14/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.26  
% 2.14/1.27  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tops_2)).
% 2.14/1.27  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.14/1.27  tff(f_34, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.14/1.27  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.14/1.27  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.14/1.27  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.14/1.27  tff(c_32, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.14/1.27  tff(c_47, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_32])).
% 2.14/1.27  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.27  tff(c_48, plain, (![A_1]: (k4_xboole_0('#skF_3', A_1)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_47, c_2])).
% 2.14/1.27  tff(c_65, plain, (![C_26, B_27]: (~r2_hidden(C_26, k4_xboole_0(B_27, k1_tarski(C_26))))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.14/1.27  tff(c_68, plain, (![C_26]: (~r2_hidden(C_26, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_65])).
% 2.14/1.27  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.14/1.27  tff(c_49, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_10])).
% 2.14/1.27  tff(c_124, plain, (![A_56, B_57, C_58]: (r2_hidden('#skF_1'(A_56, B_57, C_58), C_58) | r2_hidden(k3_subset_1(A_56, '#skF_1'(A_56, B_57, C_58)), B_57) | k7_setfam_1(A_56, B_57)=C_58 | ~m1_subset_1(C_58, k1_zfmisc_1(k1_zfmisc_1(A_56))) | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.27  tff(c_144, plain, (![A_56, C_58]: (r2_hidden('#skF_1'(A_56, '#skF_3', C_58), C_58) | k7_setfam_1(A_56, '#skF_3')=C_58 | ~m1_subset_1(C_58, k1_zfmisc_1(k1_zfmisc_1(A_56))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(resolution, [status(thm)], [c_124, c_68])).
% 2.14/1.27  tff(c_158, plain, (![A_59, C_60]: (r2_hidden('#skF_1'(A_59, '#skF_3', C_60), C_60) | k7_setfam_1(A_59, '#skF_3')=C_60 | ~m1_subset_1(C_60, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_144])).
% 2.14/1.27  tff(c_164, plain, (![A_59]: (r2_hidden('#skF_1'(A_59, '#skF_3', '#skF_3'), '#skF_3') | k7_setfam_1(A_59, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_49, c_158])).
% 2.14/1.27  tff(c_168, plain, (![A_59]: (k7_setfam_1(A_59, '#skF_3')='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_164])).
% 2.14/1.27  tff(c_38, plain, (k1_xboole_0!='#skF_3' | k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.14/1.27  tff(c_64, plain, (k7_setfam_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_47, c_38])).
% 2.14/1.27  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_64])).
% 2.14/1.27  tff(c_174, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.14/1.27  tff(c_173, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.14/1.27  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.14/1.27  tff(c_223, plain, (![A_76, B_77]: (k7_setfam_1(A_76, B_77)!=k1_xboole_0 | k1_xboole_0=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.27  tff(c_226, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_223])).
% 2.14/1.27  tff(c_233, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_226])).
% 2.14/1.27  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_233])).
% 2.14/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  Inference rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Ref     : 0
% 2.14/1.27  #Sup     : 39
% 2.14/1.27  #Fact    : 0
% 2.14/1.27  #Define  : 0
% 2.14/1.27  #Split   : 1
% 2.14/1.27  #Chain   : 0
% 2.14/1.27  #Close   : 0
% 2.14/1.27  
% 2.14/1.27  Ordering : KBO
% 2.14/1.27  
% 2.14/1.27  Simplification rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Subsume      : 6
% 2.14/1.27  #Demod        : 13
% 2.14/1.27  #Tautology    : 20
% 2.14/1.27  #SimpNegUnit  : 5
% 2.14/1.27  #BackRed      : 4
% 2.14/1.27  
% 2.14/1.27  #Partial instantiations: 0
% 2.14/1.27  #Strategies tried      : 1
% 2.14/1.27  
% 2.14/1.27  Timing (in seconds)
% 2.14/1.27  ----------------------
% 2.14/1.28  Preprocessing        : 0.31
% 2.14/1.28  Parsing              : 0.16
% 2.14/1.28  CNF conversion       : 0.02
% 2.14/1.28  Main loop            : 0.20
% 2.14/1.28  Inferencing          : 0.07
% 2.14/1.28  Reduction            : 0.05
% 2.14/1.28  Demodulation         : 0.04
% 2.14/1.28  BG Simplification    : 0.01
% 2.14/1.28  Subsumption          : 0.04
% 2.23/1.28  Abstraction          : 0.01
% 2.23/1.28  MUC search           : 0.00
% 2.23/1.28  Cooper               : 0.00
% 2.23/1.28  Total                : 0.54
% 2.23/1.28  Index Insertion      : 0.00
% 2.23/1.28  Index Deletion       : 0.00
% 2.23/1.28  Index Matching       : 0.00
% 2.23/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
