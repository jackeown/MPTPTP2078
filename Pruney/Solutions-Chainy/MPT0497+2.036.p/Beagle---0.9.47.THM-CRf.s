%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:44 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   60 (  77 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 131 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_58,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_46,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_103,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_40,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_140,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_40])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_105,plain,(
    ! [B_30,A_31] :
      ( r1_xboole_0(B_30,A_31)
      | ~ r1_xboole_0(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_103,c_105])).

tff(c_18,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_217,plain,(
    ! [A_54,B_55] :
      ( k5_relat_1(A_54,B_55) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_54),k1_relat_1(B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_220,plain,(
    ! [A_16,B_55] :
      ( k5_relat_1(k6_relat_1(A_16),B_55) = k1_xboole_0
      | ~ r1_xboole_0(A_16,k1_relat_1(B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_217])).

tff(c_239,plain,(
    ! [A_56,B_57] :
      ( k5_relat_1(k6_relat_1(A_56),B_57) = k1_xboole_0
      | ~ r1_xboole_0(A_56,k1_relat_1(B_57))
      | ~ v1_relat_1(B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_220])).

tff(c_246,plain,
    ( k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_239])).

tff(c_256,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_246])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( k5_relat_1(k6_relat_1(A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_264,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_36])).

tff(c_271,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_264])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_271])).

tff(c_275,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_96,plain,(
    ! [A_27,B_28] : ~ r2_hidden(A_27,k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_96])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_274,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_403,plain,(
    ! [A_84,C_85,B_86] :
      ( r2_hidden(A_84,k1_relat_1(k7_relat_1(C_85,B_86)))
      | ~ r2_hidden(A_84,k1_relat_1(C_85))
      | ~ r2_hidden(A_84,B_86)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_412,plain,(
    ! [A_84] :
      ( r2_hidden(A_84,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_84,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_84,'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_403])).

tff(c_416,plain,(
    ! [A_84] :
      ( r2_hidden(A_84,k1_xboole_0)
      | ~ r2_hidden(A_84,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_84,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22,c_412])).

tff(c_418,plain,(
    ! [A_87] :
      ( ~ r2_hidden(A_87,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_87,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_416])).

tff(c_684,plain,(
    ! [B_99] :
      ( ~ r2_hidden('#skF_1'(k1_relat_1('#skF_3'),B_99),'#skF_2')
      | r1_xboole_0(k1_relat_1('#skF_3'),B_99) ) ),
    inference(resolution,[status(thm)],[c_8,c_418])).

tff(c_688,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_684])).

tff(c_692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_275,c_688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:34:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.48  
% 2.77/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.48  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.77/1.48  
% 2.77/1.48  %Foreground sorts:
% 2.77/1.48  
% 2.77/1.48  
% 2.77/1.48  %Background operators:
% 2.77/1.48  
% 2.77/1.48  
% 2.77/1.48  %Foreground operators:
% 2.77/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.77/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.77/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.77/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.48  
% 2.77/1.49  tff(f_93, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.77/1.49  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.77/1.49  tff(f_58, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.77/1.49  tff(f_74, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.77/1.49  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_relat_1)).
% 2.77/1.49  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.77/1.49  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.77/1.49  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.77/1.49  tff(f_56, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.77/1.49  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.77/1.49  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.77/1.49  tff(c_46, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.77/1.49  tff(c_103, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 2.77/1.49  tff(c_40, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.77/1.49  tff(c_140, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_103, c_40])).
% 2.77/1.49  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.77/1.49  tff(c_105, plain, (![B_30, A_31]: (r1_xboole_0(B_30, A_31) | ~r1_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.49  tff(c_108, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_103, c_105])).
% 2.77/1.49  tff(c_18, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.77/1.49  tff(c_28, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.49  tff(c_217, plain, (![A_54, B_55]: (k5_relat_1(A_54, B_55)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_54), k1_relat_1(B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.77/1.49  tff(c_220, plain, (![A_16, B_55]: (k5_relat_1(k6_relat_1(A_16), B_55)=k1_xboole_0 | ~r1_xboole_0(A_16, k1_relat_1(B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_217])).
% 2.77/1.49  tff(c_239, plain, (![A_56, B_57]: (k5_relat_1(k6_relat_1(A_56), B_57)=k1_xboole_0 | ~r1_xboole_0(A_56, k1_relat_1(B_57)) | ~v1_relat_1(B_57))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_220])).
% 2.77/1.49  tff(c_246, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_239])).
% 2.77/1.49  tff(c_256, plain, (k5_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_246])).
% 2.77/1.49  tff(c_36, plain, (![A_20, B_21]: (k5_relat_1(k6_relat_1(A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.77/1.49  tff(c_264, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_256, c_36])).
% 2.77/1.49  tff(c_271, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_264])).
% 2.77/1.49  tff(c_273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_140, c_271])).
% 2.77/1.49  tff(c_275, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 2.77/1.49  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.49  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.49  tff(c_12, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.77/1.49  tff(c_96, plain, (![A_27, B_28]: (~r2_hidden(A_27, k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.77/1.49  tff(c_102, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_96])).
% 2.77/1.49  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.49  tff(c_274, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 2.77/1.49  tff(c_403, plain, (![A_84, C_85, B_86]: (r2_hidden(A_84, k1_relat_1(k7_relat_1(C_85, B_86))) | ~r2_hidden(A_84, k1_relat_1(C_85)) | ~r2_hidden(A_84, B_86) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.77/1.49  tff(c_412, plain, (![A_84]: (r2_hidden(A_84, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_84, k1_relat_1('#skF_3')) | ~r2_hidden(A_84, '#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_403])).
% 2.77/1.49  tff(c_416, plain, (![A_84]: (r2_hidden(A_84, k1_xboole_0) | ~r2_hidden(A_84, k1_relat_1('#skF_3')) | ~r2_hidden(A_84, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_22, c_412])).
% 2.77/1.49  tff(c_418, plain, (![A_87]: (~r2_hidden(A_87, k1_relat_1('#skF_3')) | ~r2_hidden(A_87, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_102, c_416])).
% 2.77/1.49  tff(c_684, plain, (![B_99]: (~r2_hidden('#skF_1'(k1_relat_1('#skF_3'), B_99), '#skF_2') | r1_xboole_0(k1_relat_1('#skF_3'), B_99))), inference(resolution, [status(thm)], [c_8, c_418])).
% 2.77/1.49  tff(c_688, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_6, c_684])).
% 2.77/1.49  tff(c_692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_275, c_688])).
% 2.77/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.49  
% 2.77/1.49  Inference rules
% 2.77/1.49  ----------------------
% 2.77/1.49  #Ref     : 0
% 2.77/1.49  #Sup     : 130
% 2.77/1.49  #Fact    : 0
% 2.77/1.49  #Define  : 0
% 2.77/1.49  #Split   : 3
% 2.77/1.49  #Chain   : 0
% 2.77/1.49  #Close   : 0
% 2.77/1.49  
% 2.77/1.49  Ordering : KBO
% 2.77/1.49  
% 2.77/1.49  Simplification rules
% 2.77/1.49  ----------------------
% 2.77/1.49  #Subsume      : 30
% 2.77/1.49  #Demod        : 86
% 2.77/1.49  #Tautology    : 63
% 2.77/1.49  #SimpNegUnit  : 10
% 2.77/1.49  #BackRed      : 0
% 2.77/1.49  
% 2.77/1.49  #Partial instantiations: 0
% 2.77/1.49  #Strategies tried      : 1
% 2.77/1.50  
% 2.77/1.50  Timing (in seconds)
% 2.77/1.50  ----------------------
% 2.77/1.50  Preprocessing        : 0.33
% 2.77/1.50  Parsing              : 0.18
% 2.77/1.50  CNF conversion       : 0.02
% 2.77/1.50  Main loop            : 0.32
% 2.77/1.50  Inferencing          : 0.12
% 2.77/1.50  Reduction            : 0.10
% 2.77/1.50  Demodulation         : 0.07
% 2.77/1.50  BG Simplification    : 0.02
% 2.77/1.50  Subsumption          : 0.07
% 2.77/1.50  Abstraction          : 0.01
% 2.77/1.50  MUC search           : 0.00
% 2.77/1.50  Cooper               : 0.00
% 2.77/1.50  Total                : 0.69
% 2.77/1.50  Index Insertion      : 0.00
% 2.77/1.50  Index Deletion       : 0.00
% 2.77/1.50  Index Matching       : 0.00
% 2.77/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
