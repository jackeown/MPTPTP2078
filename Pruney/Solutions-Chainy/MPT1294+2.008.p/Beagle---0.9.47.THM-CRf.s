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

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   43 (  79 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 ( 148 expanded)
%              Number of equality atoms :   30 ( 104 expanded)
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

tff(f_77,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_48,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(c_30,plain,
    ( k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_45,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    ! [A_1] : k4_xboole_0('#skF_3',A_1) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_45,c_2])).

tff(c_63,plain,(
    ! [B_25,A_26] :
      ( ~ r2_hidden(B_25,A_26)
      | k4_xboole_0(A_26,k1_tarski(B_25)) != A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    ! [B_25] : ~ r2_hidden(B_25,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_63])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_47,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_8])).

tff(c_118,plain,(
    ! [A_51,B_52,C_53] :
      ( r2_hidden('#skF_1'(A_51,B_52,C_53),C_53)
      | r2_hidden(k3_subset_1(A_51,'#skF_1'(A_51,B_52,C_53)),B_52)
      | k7_setfam_1(A_51,B_52) = C_53
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k1_zfmisc_1(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_134,plain,(
    ! [A_51,C_53] :
      ( r2_hidden('#skF_1'(A_51,'#skF_3',C_53),C_53)
      | k7_setfam_1(A_51,'#skF_3') = C_53
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k1_zfmisc_1(A_51)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(resolution,[status(thm)],[c_118,c_68])).

tff(c_143,plain,(
    ! [A_57,C_58] :
      ( r2_hidden('#skF_1'(A_57,'#skF_3',C_58),C_58)
      | k7_setfam_1(A_57,'#skF_3') = C_58
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_134])).

tff(c_149,plain,(
    ! [A_57] :
      ( r2_hidden('#skF_1'(A_57,'#skF_3','#skF_3'),'#skF_3')
      | k7_setfam_1(A_57,'#skF_3') = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_47,c_143])).

tff(c_153,plain,(
    ! [A_57] : k7_setfam_1(A_57,'#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_149])).

tff(c_36,plain,
    ( k1_xboole_0 != '#skF_3'
    | k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_62,plain,(
    k7_setfam_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_45,c_36])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_62])).

tff(c_159,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_158,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_210,plain,(
    ! [A_70,B_71] :
      ( k7_setfam_1(A_70,B_71) != k1_xboole_0
      | k1_xboole_0 = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(A_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_213,plain,
    ( k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_210])).

tff(c_220,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_213])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:16:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.32  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.12/1.32  
% 2.12/1.32  %Foreground sorts:
% 2.12/1.32  
% 2.12/1.32  
% 2.12/1.32  %Background operators:
% 2.12/1.32  
% 2.12/1.32  
% 2.12/1.32  %Foreground operators:
% 2.12/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.32  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.12/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.12/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.32  
% 2.12/1.33  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tops_2)).
% 2.12/1.33  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.12/1.33  tff(f_32, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.12/1.33  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.12/1.33  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.12/1.33  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.12/1.33  tff(c_30, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.12/1.33  tff(c_45, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_30])).
% 2.12/1.33  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.33  tff(c_46, plain, (![A_1]: (k4_xboole_0('#skF_3', A_1)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_45, c_2])).
% 2.12/1.33  tff(c_63, plain, (![B_25, A_26]: (~r2_hidden(B_25, A_26) | k4_xboole_0(A_26, k1_tarski(B_25))!=A_26)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.33  tff(c_68, plain, (![B_25]: (~r2_hidden(B_25, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_63])).
% 2.12/1.33  tff(c_8, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.12/1.33  tff(c_47, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_8])).
% 2.12/1.33  tff(c_118, plain, (![A_51, B_52, C_53]: (r2_hidden('#skF_1'(A_51, B_52, C_53), C_53) | r2_hidden(k3_subset_1(A_51, '#skF_1'(A_51, B_52, C_53)), B_52) | k7_setfam_1(A_51, B_52)=C_53 | ~m1_subset_1(C_53, k1_zfmisc_1(k1_zfmisc_1(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.33  tff(c_134, plain, (![A_51, C_53]: (r2_hidden('#skF_1'(A_51, '#skF_3', C_53), C_53) | k7_setfam_1(A_51, '#skF_3')=C_53 | ~m1_subset_1(C_53, k1_zfmisc_1(k1_zfmisc_1(A_51))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(resolution, [status(thm)], [c_118, c_68])).
% 2.12/1.33  tff(c_143, plain, (![A_57, C_58]: (r2_hidden('#skF_1'(A_57, '#skF_3', C_58), C_58) | k7_setfam_1(A_57, '#skF_3')=C_58 | ~m1_subset_1(C_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_134])).
% 2.12/1.33  tff(c_149, plain, (![A_57]: (r2_hidden('#skF_1'(A_57, '#skF_3', '#skF_3'), '#skF_3') | k7_setfam_1(A_57, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_47, c_143])).
% 2.12/1.33  tff(c_153, plain, (![A_57]: (k7_setfam_1(A_57, '#skF_3')='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_149])).
% 2.12/1.33  tff(c_36, plain, (k1_xboole_0!='#skF_3' | k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.12/1.33  tff(c_62, plain, (k7_setfam_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_45, c_36])).
% 2.12/1.33  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_62])).
% 2.12/1.33  tff(c_159, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.12/1.33  tff(c_158, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 2.12/1.33  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.12/1.33  tff(c_210, plain, (![A_70, B_71]: (k7_setfam_1(A_70, B_71)!=k1_xboole_0 | k1_xboole_0=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(A_70))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.33  tff(c_213, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28, c_210])).
% 2.12/1.33  tff(c_220, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_213])).
% 2.12/1.33  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_220])).
% 2.12/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.33  
% 2.12/1.33  Inference rules
% 2.12/1.33  ----------------------
% 2.12/1.33  #Ref     : 0
% 2.12/1.33  #Sup     : 36
% 2.12/1.33  #Fact    : 0
% 2.12/1.33  #Define  : 0
% 2.12/1.33  #Split   : 1
% 2.12/1.33  #Chain   : 0
% 2.12/1.33  #Close   : 0
% 2.12/1.33  
% 2.12/1.33  Ordering : KBO
% 2.12/1.33  
% 2.12/1.33  Simplification rules
% 2.12/1.33  ----------------------
% 2.12/1.33  #Subsume      : 3
% 2.12/1.33  #Demod        : 13
% 2.12/1.33  #Tautology    : 25
% 2.12/1.33  #SimpNegUnit  : 4
% 2.12/1.33  #BackRed      : 4
% 2.12/1.33  
% 2.12/1.33  #Partial instantiations: 0
% 2.12/1.33  #Strategies tried      : 1
% 2.12/1.33  
% 2.12/1.33  Timing (in seconds)
% 2.12/1.33  ----------------------
% 2.12/1.33  Preprocessing        : 0.33
% 2.12/1.33  Parsing              : 0.17
% 2.12/1.33  CNF conversion       : 0.02
% 2.12/1.33  Main loop            : 0.18
% 2.12/1.33  Inferencing          : 0.07
% 2.12/1.33  Reduction            : 0.05
% 2.12/1.33  Demodulation         : 0.04
% 2.12/1.33  BG Simplification    : 0.01
% 2.12/1.33  Subsumption          : 0.03
% 2.12/1.33  Abstraction          : 0.01
% 2.12/1.33  MUC search           : 0.00
% 2.12/1.33  Cooper               : 0.00
% 2.12/1.33  Total                : 0.54
% 2.12/1.33  Index Insertion      : 0.00
% 2.12/1.33  Index Deletion       : 0.00
% 2.12/1.33  Index Matching       : 0.00
% 2.12/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
