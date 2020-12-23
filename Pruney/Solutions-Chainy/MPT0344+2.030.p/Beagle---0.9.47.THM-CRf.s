%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:23 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 113 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   78 ( 235 expanded)
%              Number of equality atoms :   24 (  65 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ~ ( B != k1_xboole_0
            & ! [C] :
                ( m1_subset_1(C,A)
               => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_37,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    ! [B_21,A_22] :
      ( m1_subset_1(B_21,A_22)
      | ~ v1_xboole_0(B_21)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [C_20] :
      ( ~ r2_hidden(C_20,'#skF_3')
      | ~ m1_subset_1(C_20,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4,c_28])).

tff(c_35,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_32])).

tff(c_40,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_35])).

tff(c_41,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_129,plain,(
    ! [C_37,A_38,B_39] :
      ( r2_hidden(C_37,A_38)
      | ~ r2_hidden(C_37,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_136,plain,(
    ! [A_40,A_41] :
      ( r2_hidden('#skF_1'(A_40),A_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(A_41))
      | k1_xboole_0 = A_40 ) ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_237,plain,(
    ! [A_50,A_51] :
      ( m1_subset_1('#skF_1'(A_50),A_51)
      | v1_xboole_0(A_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(A_51))
      | k1_xboole_0 = A_50 ) ),
    inference(resolution,[status(thm)],[c_136,c_10])).

tff(c_264,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_237,c_35])).

tff(c_279,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_264])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_41,c_279])).

tff(c_283,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_287,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_283,c_2])).

tff(c_291,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_22])).

tff(c_288,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | A_2 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_4])).

tff(c_406,plain,(
    ! [C_71,A_72,B_73] :
      ( r2_hidden(C_71,A_72)
      | ~ r2_hidden(C_71,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_413,plain,(
    ! [A_74,A_75] :
      ( r2_hidden('#skF_1'(A_74),A_75)
      | ~ m1_subset_1(A_74,k1_zfmisc_1(A_75))
      | A_74 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_288,c_406])).

tff(c_320,plain,(
    ! [A_58,B_59] :
      ( k2_xboole_0(k1_tarski(A_58),B_59) = B_59
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),B_7) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_289,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),B_7) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_8])).

tff(c_325,plain,(
    ! [B_59,A_58] :
      ( B_59 != '#skF_2'
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_289])).

tff(c_431,plain,(
    ! [A_76,A_77] :
      ( A_76 != '#skF_2'
      | ~ m1_subset_1(A_77,k1_zfmisc_1(A_76))
      | A_77 = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_413,c_325])).

tff(c_442,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_431])).

tff(c_448,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.32  
% 2.11/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.32  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.11/1.32  
% 2.11/1.32  %Foreground sorts:
% 2.11/1.32  
% 2.11/1.32  
% 2.11/1.32  %Background operators:
% 2.11/1.32  
% 2.11/1.32  
% 2.11/1.32  %Foreground operators:
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.32  
% 2.11/1.33  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.11/1.33  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.11/1.33  tff(f_37, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.11/1.33  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.11/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.11/1.33  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.11/1.33  tff(f_44, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.11/1.33  tff(c_22, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.33  tff(c_36, plain, (![B_21, A_22]: (m1_subset_1(B_21, A_22) | ~v1_xboole_0(B_21) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.11/1.33  tff(c_4, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.33  tff(c_28, plain, (![C_20]: (~r2_hidden(C_20, '#skF_3') | ~m1_subset_1(C_20, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.33  tff(c_32, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_2') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4, c_28])).
% 2.11/1.33  tff(c_35, plain, (~m1_subset_1('#skF_1'('#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_22, c_32])).
% 2.11/1.33  tff(c_40, plain, (~v1_xboole_0('#skF_1'('#skF_3')) | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_35])).
% 2.11/1.33  tff(c_41, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_40])).
% 2.11/1.33  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.11/1.33  tff(c_129, plain, (![C_37, A_38, B_39]: (r2_hidden(C_37, A_38) | ~r2_hidden(C_37, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.33  tff(c_136, plain, (![A_40, A_41]: (r2_hidden('#skF_1'(A_40), A_41) | ~m1_subset_1(A_40, k1_zfmisc_1(A_41)) | k1_xboole_0=A_40)), inference(resolution, [status(thm)], [c_4, c_129])).
% 2.11/1.33  tff(c_10, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~r2_hidden(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.11/1.33  tff(c_237, plain, (![A_50, A_51]: (m1_subset_1('#skF_1'(A_50), A_51) | v1_xboole_0(A_51) | ~m1_subset_1(A_50, k1_zfmisc_1(A_51)) | k1_xboole_0=A_50)), inference(resolution, [status(thm)], [c_136, c_10])).
% 2.11/1.33  tff(c_264, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')) | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_237, c_35])).
% 2.11/1.33  tff(c_279, plain, (v1_xboole_0('#skF_2') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_264])).
% 2.11/1.33  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_41, c_279])).
% 2.11/1.33  tff(c_283, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 2.11/1.33  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.33  tff(c_287, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_283, c_2])).
% 2.11/1.33  tff(c_291, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_287, c_22])).
% 2.11/1.33  tff(c_288, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | A_2='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_4])).
% 2.11/1.33  tff(c_406, plain, (![C_71, A_72, B_73]: (r2_hidden(C_71, A_72) | ~r2_hidden(C_71, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.11/1.33  tff(c_413, plain, (![A_74, A_75]: (r2_hidden('#skF_1'(A_74), A_75) | ~m1_subset_1(A_74, k1_zfmisc_1(A_75)) | A_74='#skF_2')), inference(resolution, [status(thm)], [c_288, c_406])).
% 2.11/1.33  tff(c_320, plain, (![A_58, B_59]: (k2_xboole_0(k1_tarski(A_58), B_59)=B_59 | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.33  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.11/1.33  tff(c_289, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), B_7)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_8])).
% 2.11/1.33  tff(c_325, plain, (![B_59, A_58]: (B_59!='#skF_2' | ~r2_hidden(A_58, B_59))), inference(superposition, [status(thm), theory('equality')], [c_320, c_289])).
% 2.11/1.33  tff(c_431, plain, (![A_76, A_77]: (A_76!='#skF_2' | ~m1_subset_1(A_77, k1_zfmisc_1(A_76)) | A_77='#skF_2')), inference(resolution, [status(thm)], [c_413, c_325])).
% 2.11/1.33  tff(c_442, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_24, c_431])).
% 2.11/1.33  tff(c_448, plain, $false, inference(negUnitSimplification, [status(thm)], [c_291, c_442])).
% 2.11/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.33  
% 2.11/1.33  Inference rules
% 2.11/1.33  ----------------------
% 2.11/1.33  #Ref     : 0
% 2.11/1.33  #Sup     : 82
% 2.11/1.33  #Fact    : 0
% 2.11/1.33  #Define  : 0
% 2.11/1.33  #Split   : 8
% 2.11/1.33  #Chain   : 0
% 2.11/1.33  #Close   : 0
% 2.11/1.33  
% 2.11/1.33  Ordering : KBO
% 2.11/1.33  
% 2.11/1.33  Simplification rules
% 2.11/1.33  ----------------------
% 2.11/1.33  #Subsume      : 14
% 2.11/1.33  #Demod        : 7
% 2.11/1.33  #Tautology    : 20
% 2.11/1.33  #SimpNegUnit  : 16
% 2.11/1.33  #BackRed      : 4
% 2.11/1.33  
% 2.11/1.33  #Partial instantiations: 0
% 2.11/1.33  #Strategies tried      : 1
% 2.11/1.33  
% 2.11/1.33  Timing (in seconds)
% 2.11/1.33  ----------------------
% 2.11/1.33  Preprocessing        : 0.29
% 2.11/1.33  Parsing              : 0.16
% 2.11/1.34  CNF conversion       : 0.02
% 2.11/1.34  Main loop            : 0.25
% 2.11/1.34  Inferencing          : 0.10
% 2.11/1.34  Reduction            : 0.06
% 2.11/1.34  Demodulation         : 0.03
% 2.11/1.34  BG Simplification    : 0.01
% 2.11/1.34  Subsumption          : 0.06
% 2.11/1.34  Abstraction          : 0.01
% 2.11/1.34  MUC search           : 0.00
% 2.11/1.34  Cooper               : 0.00
% 2.11/1.34  Total                : 0.56
% 2.11/1.34  Index Insertion      : 0.00
% 2.11/1.34  Index Deletion       : 0.00
% 2.11/1.34  Index Matching       : 0.00
% 2.11/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
