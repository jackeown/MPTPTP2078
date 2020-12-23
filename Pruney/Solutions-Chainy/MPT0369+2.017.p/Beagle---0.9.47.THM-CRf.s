%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:53 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   53 (  65 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 116 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    m1_subset_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_59,plain,(
    ! [B_31,A_32] :
      ( v1_xboole_0(B_31)
      | ~ m1_subset_1(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_67,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_59])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( r2_hidden(B_21,A_20)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_216,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = k3_subset_1(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_230,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_216])).

tff(c_328,plain,(
    ! [D_69,A_70,B_71] :
      ( r2_hidden(D_69,k4_xboole_0(A_70,B_71))
      | r2_hidden(D_69,B_71)
      | ~ r2_hidden(D_69,A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_386,plain,(
    ! [D_73] :
      ( r2_hidden(D_73,k3_subset_1('#skF_5','#skF_6'))
      | r2_hidden(D_73,'#skF_6')
      | ~ r2_hidden(D_73,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_328])).

tff(c_44,plain,(
    ~ r2_hidden('#skF_7',k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_407,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_386,c_44])).

tff(c_418,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_407])).

tff(c_421,plain,
    ( ~ m1_subset_1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_418])).

tff(c_424,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_421])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_424])).

tff(c_428,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_503,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_2'(A_90,B_91),A_90)
      | r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_523,plain,(
    ! [A_93,B_94] :
      ( ~ v1_xboole_0(A_93)
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_503,c_2])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k4_xboole_0(B_19,A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_529,plain,(
    ! [A_95] :
      ( k1_xboole_0 = A_95
      | ~ v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_523,c_32])).

tff(c_532,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_428,c_529])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:13:37 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.34  
% 2.45/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.34  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 2.45/1.34  
% 2.45/1.34  %Foreground sorts:
% 2.45/1.34  
% 2.45/1.34  
% 2.45/1.34  %Background operators:
% 2.45/1.34  
% 2.45/1.34  
% 2.45/1.34  %Foreground operators:
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.45/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.45/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.45/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.45/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.45/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.45/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.45/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.45/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.45/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.34  
% 2.45/1.35  tff(f_86, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.45/1.35  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.45/1.35  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.45/1.35  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.45/1.35  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.45/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.45/1.35  tff(f_54, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.45/1.35  tff(c_52, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.45/1.35  tff(c_48, plain, (m1_subset_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.45/1.35  tff(c_59, plain, (![B_31, A_32]: (v1_xboole_0(B_31) | ~m1_subset_1(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.45/1.35  tff(c_67, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_59])).
% 2.45/1.35  tff(c_68, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_67])).
% 2.45/1.35  tff(c_36, plain, (![B_21, A_20]: (r2_hidden(B_21, A_20) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.45/1.35  tff(c_46, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.45/1.35  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.45/1.35  tff(c_216, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=k3_subset_1(A_63, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.35  tff(c_230, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_216])).
% 2.45/1.35  tff(c_328, plain, (![D_69, A_70, B_71]: (r2_hidden(D_69, k4_xboole_0(A_70, B_71)) | r2_hidden(D_69, B_71) | ~r2_hidden(D_69, A_70))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.45/1.35  tff(c_386, plain, (![D_73]: (r2_hidden(D_73, k3_subset_1('#skF_5', '#skF_6')) | r2_hidden(D_73, '#skF_6') | ~r2_hidden(D_73, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_230, c_328])).
% 2.45/1.35  tff(c_44, plain, (~r2_hidden('#skF_7', k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.45/1.35  tff(c_407, plain, (r2_hidden('#skF_7', '#skF_6') | ~r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_386, c_44])).
% 2.45/1.35  tff(c_418, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_407])).
% 2.45/1.35  tff(c_421, plain, (~m1_subset_1('#skF_7', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_418])).
% 2.45/1.35  tff(c_424, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_421])).
% 2.45/1.35  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_424])).
% 2.45/1.35  tff(c_428, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_67])).
% 2.45/1.35  tff(c_503, plain, (![A_90, B_91]: (r2_hidden('#skF_2'(A_90, B_91), A_90) | r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.45/1.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.45/1.35  tff(c_523, plain, (![A_93, B_94]: (~v1_xboole_0(A_93) | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_503, c_2])).
% 2.45/1.35  tff(c_32, plain, (![A_18, B_19]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, k4_xboole_0(B_19, A_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.45/1.35  tff(c_529, plain, (![A_95]: (k1_xboole_0=A_95 | ~v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_523, c_32])).
% 2.45/1.35  tff(c_532, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_428, c_529])).
% 2.45/1.35  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_532])).
% 2.45/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.35  
% 2.45/1.35  Inference rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Ref     : 0
% 2.45/1.35  #Sup     : 98
% 2.45/1.35  #Fact    : 0
% 2.45/1.35  #Define  : 0
% 2.45/1.35  #Split   : 10
% 2.45/1.35  #Chain   : 0
% 2.45/1.35  #Close   : 0
% 2.45/1.35  
% 2.45/1.35  Ordering : KBO
% 2.45/1.35  
% 2.45/1.35  Simplification rules
% 2.45/1.35  ----------------------
% 2.45/1.35  #Subsume      : 7
% 2.45/1.35  #Demod        : 4
% 2.45/1.35  #Tautology    : 22
% 2.45/1.35  #SimpNegUnit  : 12
% 2.45/1.35  #BackRed      : 0
% 2.45/1.35  
% 2.45/1.35  #Partial instantiations: 0
% 2.45/1.35  #Strategies tried      : 1
% 2.45/1.35  
% 2.45/1.35  Timing (in seconds)
% 2.45/1.35  ----------------------
% 2.45/1.36  Preprocessing        : 0.33
% 2.45/1.36  Parsing              : 0.17
% 2.45/1.36  CNF conversion       : 0.03
% 2.45/1.36  Main loop            : 0.29
% 2.45/1.36  Inferencing          : 0.10
% 2.45/1.36  Reduction            : 0.07
% 2.45/1.36  Demodulation         : 0.04
% 2.45/1.36  BG Simplification    : 0.02
% 2.45/1.36  Subsumption          : 0.06
% 2.45/1.36  Abstraction          : 0.01
% 2.45/1.36  MUC search           : 0.00
% 2.45/1.36  Cooper               : 0.00
% 2.45/1.36  Total                : 0.65
% 2.45/1.36  Index Insertion      : 0.00
% 2.45/1.36  Index Deletion       : 0.00
% 2.45/1.36  Index Matching       : 0.00
% 2.45/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
