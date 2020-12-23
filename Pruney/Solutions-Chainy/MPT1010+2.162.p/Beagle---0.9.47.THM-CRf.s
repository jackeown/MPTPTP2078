%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:27 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   53 (  57 expanded)
%              Number of leaves         :   33 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  77 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_44,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    ! [A_37] : k2_zfmisc_1(A_37,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_85,plain,(
    ! [A_49,B_50] : ~ r2_hidden(A_49,k2_zfmisc_1(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_88,plain,(
    ! [A_37] : ~ r2_hidden(A_37,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_85])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(A_57,B_58)
      | k4_xboole_0(k1_tarski(A_57),B_58) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_121,plain,(
    ! [A_57] :
      ( r2_hidden(A_57,k1_xboole_0)
      | k1_tarski(A_57) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_122,plain,(
    ! [A_57] : k1_tarski(A_57) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_121])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_268,plain,(
    ! [D_102,C_103,B_104,A_105] :
      ( r2_hidden(k1_funct_1(D_102,C_103),B_104)
      | k1_xboole_0 = B_104
      | ~ r2_hidden(C_103,A_105)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104)))
      | ~ v1_funct_2(D_102,A_105,B_104)
      | ~ v1_funct_1(D_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_281,plain,(
    ! [D_106,B_107] :
      ( r2_hidden(k1_funct_1(D_106,'#skF_5'),B_107)
      | k1_xboole_0 = B_107
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_107)))
      | ~ v1_funct_2(D_106,'#skF_3',B_107)
      | ~ v1_funct_1(D_106) ) ),
    inference(resolution,[status(thm)],[c_46,c_268])).

tff(c_284,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_281])).

tff(c_291,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_284])).

tff(c_292,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_291])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_299,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_292,c_4])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.26  
% 2.24/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.27  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.24/1.27  
% 2.24/1.27  %Foreground sorts:
% 2.24/1.27  
% 2.24/1.27  
% 2.24/1.27  %Background operators:
% 2.24/1.27  
% 2.24/1.27  
% 2.24/1.27  %Foreground operators:
% 2.24/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.24/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.24/1.27  tff('#skF_6', type, '#skF_6': $i).
% 2.24/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.24/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.24/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.24/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.24/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.27  
% 2.24/1.28  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.24/1.28  tff(f_58, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.24/1.28  tff(f_61, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.24/1.28  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.24/1.28  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 2.24/1.28  tff(f_73, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.24/1.28  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.24/1.28  tff(c_44, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.28  tff(c_36, plain, (![A_37]: (k2_zfmisc_1(A_37, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.24/1.28  tff(c_85, plain, (![A_49, B_50]: (~r2_hidden(A_49, k2_zfmisc_1(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.24/1.28  tff(c_88, plain, (![A_37]: (~r2_hidden(A_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_85])).
% 2.24/1.28  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.28  tff(c_117, plain, (![A_57, B_58]: (r2_hidden(A_57, B_58) | k4_xboole_0(k1_tarski(A_57), B_58)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.24/1.28  tff(c_121, plain, (![A_57]: (r2_hidden(A_57, k1_xboole_0) | k1_tarski(A_57)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_117])).
% 2.24/1.28  tff(c_122, plain, (![A_57]: (k1_tarski(A_57)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_88, c_121])).
% 2.24/1.28  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.28  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.28  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.28  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.24/1.28  tff(c_268, plain, (![D_102, C_103, B_104, A_105]: (r2_hidden(k1_funct_1(D_102, C_103), B_104) | k1_xboole_0=B_104 | ~r2_hidden(C_103, A_105) | ~m1_subset_1(D_102, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))) | ~v1_funct_2(D_102, A_105, B_104) | ~v1_funct_1(D_102))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.24/1.28  tff(c_281, plain, (![D_106, B_107]: (r2_hidden(k1_funct_1(D_106, '#skF_5'), B_107) | k1_xboole_0=B_107 | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_107))) | ~v1_funct_2(D_106, '#skF_3', B_107) | ~v1_funct_1(D_106))), inference(resolution, [status(thm)], [c_46, c_268])).
% 2.24/1.28  tff(c_284, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_281])).
% 2.24/1.28  tff(c_291, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_284])).
% 2.24/1.28  tff(c_292, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_122, c_291])).
% 2.24/1.28  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.24/1.28  tff(c_299, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_292, c_4])).
% 2.24/1.28  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_299])).
% 2.24/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.28  
% 2.24/1.28  Inference rules
% 2.24/1.28  ----------------------
% 2.24/1.28  #Ref     : 0
% 2.24/1.28  #Sup     : 53
% 2.24/1.28  #Fact    : 0
% 2.24/1.28  #Define  : 0
% 2.24/1.28  #Split   : 0
% 2.24/1.28  #Chain   : 0
% 2.24/1.28  #Close   : 0
% 2.24/1.28  
% 2.24/1.28  Ordering : KBO
% 2.24/1.28  
% 2.24/1.28  Simplification rules
% 2.24/1.28  ----------------------
% 2.24/1.28  #Subsume      : 5
% 2.24/1.28  #Demod        : 5
% 2.24/1.28  #Tautology    : 36
% 2.24/1.28  #SimpNegUnit  : 9
% 2.24/1.28  #BackRed      : 0
% 2.24/1.28  
% 2.24/1.28  #Partial instantiations: 0
% 2.24/1.28  #Strategies tried      : 1
% 2.24/1.28  
% 2.24/1.28  Timing (in seconds)
% 2.24/1.28  ----------------------
% 2.24/1.28  Preprocessing        : 0.32
% 2.24/1.28  Parsing              : 0.17
% 2.24/1.28  CNF conversion       : 0.02
% 2.24/1.28  Main loop            : 0.20
% 2.24/1.28  Inferencing          : 0.08
% 2.24/1.28  Reduction            : 0.06
% 2.24/1.28  Demodulation         : 0.04
% 2.24/1.28  BG Simplification    : 0.02
% 2.24/1.28  Subsumption          : 0.04
% 2.24/1.28  Abstraction          : 0.02
% 2.24/1.28  MUC search           : 0.00
% 2.24/1.28  Cooper               : 0.00
% 2.24/1.28  Total                : 0.55
% 2.24/1.28  Index Insertion      : 0.00
% 2.24/1.28  Index Deletion       : 0.00
% 2.24/1.28  Index Matching       : 0.00
% 2.24/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
