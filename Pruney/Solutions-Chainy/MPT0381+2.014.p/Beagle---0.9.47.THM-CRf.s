%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:03 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 165 expanded)
%              Number of leaves         :   28 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :   72 ( 299 expanded)
%              Number of equality atoms :   11 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    ! [D_50,A_51,B_52] :
      ( r2_hidden(D_50,A_51)
      | ~ r2_hidden(D_50,k4_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_275,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_74,B_75)),A_74)
      | v1_xboole_0(k4_xboole_0(A_74,B_75)) ) ),
    inference(resolution,[status(thm)],[c_4,c_140])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_293,plain,(
    ! [A_74,B_75] :
      ( ~ v1_xboole_0(A_74)
      | v1_xboole_0(k4_xboole_0(A_74,B_75)) ) ),
    inference(resolution,[status(thm)],[c_275,c_2])).

tff(c_50,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_69,plain,(
    ! [B_33,A_34] :
      ( ~ r2_hidden(B_33,A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_69])).

tff(c_294,plain,(
    ! [A_76,B_77] :
      ( ~ v1_xboole_0(A_76)
      | v1_xboole_0(k4_xboole_0(A_76,B_77)) ) ),
    inference(resolution,[status(thm)],[c_275,c_2])).

tff(c_116,plain,(
    ! [B_47,A_48] :
      ( m1_subset_1(B_47,A_48)
      | ~ r2_hidden(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_125,plain,
    ( m1_subset_1('#skF_5','#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_116])).

tff(c_130,plain,(
    m1_subset_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_125])).

tff(c_205,plain,(
    ! [B_62,A_63] :
      ( m1_subset_1(k1_tarski(B_62),k1_zfmisc_1(A_63))
      | k1_xboole_0 = A_63
      | ~ m1_subset_1(B_62,A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    ~ m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_211,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ m1_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_205,c_48])).

tff(c_215,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_211])).

tff(c_79,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_4'(A_36),A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_83,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_227,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(A_36)
      | A_36 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_83])).

tff(c_299,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = '#skF_6'
      | ~ v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_294,c_227])).

tff(c_314,plain,(
    ! [A_83,B_84,B_85] :
      ( k4_xboole_0(k4_xboole_0(A_83,B_84),B_85) = '#skF_6'
      | ~ v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_293,c_299])).

tff(c_323,plain,(
    ! [A_83,B_84] :
      ( ~ v1_xboole_0(k4_xboole_0(A_83,B_84))
      | v1_xboole_0('#skF_6')
      | ~ v1_xboole_0(A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_293])).

tff(c_345,plain,(
    ! [A_86,B_87] :
      ( ~ v1_xboole_0(k4_xboole_0(A_86,B_87))
      | ~ v1_xboole_0(A_86) ) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_323])).

tff(c_352,plain,(
    ! [A_74] : ~ v1_xboole_0(A_74) ),
    inference(resolution,[status(thm)],[c_293,c_345])).

tff(c_362,plain,(
    ! [A_89] : r2_hidden('#skF_1'(A_89),A_89) ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_4])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( r2_hidden(D_10,A_5)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_371,plain,(
    ! [A_5,B_6] : r2_hidden('#skF_1'(k4_xboole_0(A_5,B_6)),A_5) ),
    inference(resolution,[status(thm)],[c_362,c_10])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_428,plain,(
    ! [A_97,B_98] : ~ r2_hidden('#skF_1'(k4_xboole_0(A_97,B_98)),B_98) ),
    inference(resolution,[status(thm)],[c_362,c_8])).

tff(c_441,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_371,c_428])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:03:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  
% 2.31/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_4 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.31/1.29  
% 2.31/1.29  %Foreground sorts:
% 2.31/1.29  
% 2.31/1.29  
% 2.31/1.29  %Background operators:
% 2.31/1.29  
% 2.31/1.29  
% 2.31/1.29  %Foreground operators:
% 2.31/1.29  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.31/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.31/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.31/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.29  
% 2.31/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.31/1.30  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.31/1.30  tff(f_86, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.31/1.30  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.31/1.30  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.31/1.30  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.31/1.30  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.30  tff(c_140, plain, (![D_50, A_51, B_52]: (r2_hidden(D_50, A_51) | ~r2_hidden(D_50, k4_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.30  tff(c_275, plain, (![A_74, B_75]: (r2_hidden('#skF_1'(k4_xboole_0(A_74, B_75)), A_74) | v1_xboole_0(k4_xboole_0(A_74, B_75)))), inference(resolution, [status(thm)], [c_4, c_140])).
% 2.31/1.30  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.30  tff(c_293, plain, (![A_74, B_75]: (~v1_xboole_0(A_74) | v1_xboole_0(k4_xboole_0(A_74, B_75)))), inference(resolution, [status(thm)], [c_275, c_2])).
% 2.31/1.30  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.31/1.30  tff(c_69, plain, (![B_33, A_34]: (~r2_hidden(B_33, A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.30  tff(c_73, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_50, c_69])).
% 2.31/1.30  tff(c_294, plain, (![A_76, B_77]: (~v1_xboole_0(A_76) | v1_xboole_0(k4_xboole_0(A_76, B_77)))), inference(resolution, [status(thm)], [c_275, c_2])).
% 2.31/1.30  tff(c_116, plain, (![B_47, A_48]: (m1_subset_1(B_47, A_48) | ~r2_hidden(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.31/1.30  tff(c_125, plain, (m1_subset_1('#skF_5', '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_50, c_116])).
% 2.31/1.30  tff(c_130, plain, (m1_subset_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_73, c_125])).
% 2.31/1.30  tff(c_205, plain, (![B_62, A_63]: (m1_subset_1(k1_tarski(B_62), k1_zfmisc_1(A_63)) | k1_xboole_0=A_63 | ~m1_subset_1(B_62, A_63))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.30  tff(c_48, plain, (~m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.31/1.30  tff(c_211, plain, (k1_xboole_0='#skF_6' | ~m1_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_205, c_48])).
% 2.31/1.30  tff(c_215, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_211])).
% 2.31/1.30  tff(c_79, plain, (![A_36]: (r2_hidden('#skF_4'(A_36), A_36) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.31/1.30  tff(c_83, plain, (![A_36]: (~v1_xboole_0(A_36) | k1_xboole_0=A_36)), inference(resolution, [status(thm)], [c_79, c_2])).
% 2.31/1.30  tff(c_227, plain, (![A_36]: (~v1_xboole_0(A_36) | A_36='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_83])).
% 2.31/1.30  tff(c_299, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)='#skF_6' | ~v1_xboole_0(A_78))), inference(resolution, [status(thm)], [c_294, c_227])).
% 2.31/1.30  tff(c_314, plain, (![A_83, B_84, B_85]: (k4_xboole_0(k4_xboole_0(A_83, B_84), B_85)='#skF_6' | ~v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_293, c_299])).
% 2.31/1.30  tff(c_323, plain, (![A_83, B_84]: (~v1_xboole_0(k4_xboole_0(A_83, B_84)) | v1_xboole_0('#skF_6') | ~v1_xboole_0(A_83))), inference(superposition, [status(thm), theory('equality')], [c_314, c_293])).
% 2.31/1.30  tff(c_345, plain, (![A_86, B_87]: (~v1_xboole_0(k4_xboole_0(A_86, B_87)) | ~v1_xboole_0(A_86))), inference(negUnitSimplification, [status(thm)], [c_73, c_323])).
% 2.31/1.30  tff(c_352, plain, (![A_74]: (~v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_293, c_345])).
% 2.31/1.30  tff(c_362, plain, (![A_89]: (r2_hidden('#skF_1'(A_89), A_89))), inference(negUnitSimplification, [status(thm)], [c_352, c_4])).
% 2.31/1.30  tff(c_10, plain, (![D_10, A_5, B_6]: (r2_hidden(D_10, A_5) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.30  tff(c_371, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(k4_xboole_0(A_5, B_6)), A_5))), inference(resolution, [status(thm)], [c_362, c_10])).
% 2.31/1.30  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.31/1.30  tff(c_428, plain, (![A_97, B_98]: (~r2_hidden('#skF_1'(k4_xboole_0(A_97, B_98)), B_98))), inference(resolution, [status(thm)], [c_362, c_8])).
% 2.31/1.30  tff(c_441, plain, $false, inference(resolution, [status(thm)], [c_371, c_428])).
% 2.31/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.30  
% 2.31/1.30  Inference rules
% 2.31/1.30  ----------------------
% 2.31/1.30  #Ref     : 0
% 2.31/1.30  #Sup     : 82
% 2.31/1.30  #Fact    : 0
% 2.31/1.30  #Define  : 0
% 2.31/1.30  #Split   : 1
% 2.31/1.30  #Chain   : 0
% 2.31/1.30  #Close   : 0
% 2.31/1.30  
% 2.31/1.30  Ordering : KBO
% 2.31/1.30  
% 2.31/1.30  Simplification rules
% 2.31/1.30  ----------------------
% 2.31/1.30  #Subsume      : 16
% 2.31/1.30  #Demod        : 7
% 2.31/1.30  #Tautology    : 28
% 2.31/1.30  #SimpNegUnit  : 10
% 2.31/1.30  #BackRed      : 10
% 2.31/1.30  
% 2.31/1.30  #Partial instantiations: 0
% 2.31/1.30  #Strategies tried      : 1
% 2.31/1.30  
% 2.31/1.30  Timing (in seconds)
% 2.31/1.30  ----------------------
% 2.31/1.31  Preprocessing        : 0.32
% 2.31/1.31  Parsing              : 0.16
% 2.31/1.31  CNF conversion       : 0.02
% 2.31/1.31  Main loop            : 0.24
% 2.31/1.31  Inferencing          : 0.09
% 2.31/1.31  Reduction            : 0.06
% 2.31/1.31  Demodulation         : 0.04
% 2.31/1.31  BG Simplification    : 0.02
% 2.31/1.31  Subsumption          : 0.05
% 2.31/1.31  Abstraction          : 0.02
% 2.31/1.31  MUC search           : 0.00
% 2.31/1.31  Cooper               : 0.00
% 2.31/1.31  Total                : 0.59
% 2.31/1.31  Index Insertion      : 0.00
% 2.31/1.31  Index Deletion       : 0.00
% 2.31/1.31  Index Matching       : 0.00
% 2.31/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
