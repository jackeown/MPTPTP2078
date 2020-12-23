%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:06 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   61 (  83 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   79 ( 119 expanded)
%              Number of equality atoms :   21 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_46,plain,(
    ! [A_19] : k1_subset_1(A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_56,plain,
    ( k1_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_64,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56])).

tff(c_76,plain,(
    ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_63,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_62])).

tff(c_82,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_63])).

tff(c_24,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,(
    ! [A_11] : r1_tarski('#skF_7',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_24])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_76])).

tff(c_93,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_94,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [C_16,A_12] :
      ( r2_hidden(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_166,plain,(
    ! [B_53,A_54] :
      ( m1_subset_1(B_53,A_54)
      | ~ r2_hidden(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_172,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(resolution,[status(thm)],[c_28,c_166])).

tff(c_179,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_172])).

tff(c_190,plain,(
    ! [C_57,A_58,B_59] :
      ( r2_hidden(C_57,A_58)
      | ~ r2_hidden(C_57,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_671,plain,(
    ! [A_96,A_97] :
      ( r2_hidden('#skF_3'(A_96),A_97)
      | ~ m1_subset_1(A_96,k1_zfmisc_1(A_97))
      | k1_xboole_0 = A_96 ) ),
    inference(resolution,[status(thm)],[c_20,c_190])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_212,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = k3_subset_1(A_62,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_232,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_212])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_236,plain,(
    ! [D_6] :
      ( ~ r2_hidden(D_6,'#skF_7')
      | ~ r2_hidden(D_6,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_4])).

tff(c_1469,plain,(
    ! [A_121] :
      ( ~ r2_hidden('#skF_3'(A_121),'#skF_7')
      | ~ m1_subset_1(A_121,k1_zfmisc_1(k3_subset_1('#skF_6','#skF_7')))
      | k1_xboole_0 = A_121 ) ),
    inference(resolution,[status(thm)],[c_671,c_236])).

tff(c_2272,plain,(
    ! [C_170] :
      ( ~ r2_hidden('#skF_3'(C_170),'#skF_7')
      | k1_xboole_0 = C_170
      | ~ r1_tarski(C_170,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_179,c_1469])).

tff(c_2298,plain,
    ( ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_20,c_2272])).

tff(c_2310,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2298])).

tff(c_2312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_2310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.64  
% 3.78/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.64  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 3.78/1.64  
% 3.78/1.64  %Foreground sorts:
% 3.78/1.64  
% 3.78/1.64  
% 3.78/1.64  %Background operators:
% 3.78/1.64  
% 3.78/1.64  
% 3.78/1.64  %Foreground operators:
% 3.78/1.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.78/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.78/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.78/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.78/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.78/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.64  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.78/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.78/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.78/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.78/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.64  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.78/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.64  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.78/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.78/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.78/1.64  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.78/1.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.78/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.78/1.64  
% 3.78/1.66  tff(f_69, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.78/1.66  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.78/1.66  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.78/1.66  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.78/1.66  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.78/1.66  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.78/1.66  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.78/1.66  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.78/1.66  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.78/1.66  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.78/1.66  tff(c_46, plain, (![A_19]: (k1_subset_1(A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.78/1.66  tff(c_56, plain, (k1_subset_1('#skF_6')!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.78/1.66  tff(c_64, plain, (k1_xboole_0!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56])).
% 3.78/1.66  tff(c_76, plain, (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_64])).
% 3.78/1.66  tff(c_62, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.78/1.66  tff(c_63, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_62])).
% 3.78/1.66  tff(c_82, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_76, c_63])).
% 3.78/1.66  tff(c_24, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.78/1.66  tff(c_84, plain, (![A_11]: (r1_tarski('#skF_7', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_24])).
% 3.78/1.66  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_76])).
% 3.78/1.66  tff(c_93, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_64])).
% 3.78/1.66  tff(c_94, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_64])).
% 3.78/1.66  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.78/1.66  tff(c_50, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.78/1.66  tff(c_28, plain, (![C_16, A_12]: (r2_hidden(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.78/1.66  tff(c_166, plain, (![B_53, A_54]: (m1_subset_1(B_53, A_54) | ~r2_hidden(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.78/1.66  tff(c_172, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(resolution, [status(thm)], [c_28, c_166])).
% 3.78/1.66  tff(c_179, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(negUnitSimplification, [status(thm)], [c_50, c_172])).
% 3.78/1.66  tff(c_190, plain, (![C_57, A_58, B_59]: (r2_hidden(C_57, A_58) | ~r2_hidden(C_57, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.78/1.66  tff(c_671, plain, (![A_96, A_97]: (r2_hidden('#skF_3'(A_96), A_97) | ~m1_subset_1(A_96, k1_zfmisc_1(A_97)) | k1_xboole_0=A_96)), inference(resolution, [status(thm)], [c_20, c_190])).
% 3.78/1.66  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.78/1.66  tff(c_212, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=k3_subset_1(A_62, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.78/1.66  tff(c_232, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_212])).
% 3.78/1.66  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.78/1.66  tff(c_236, plain, (![D_6]: (~r2_hidden(D_6, '#skF_7') | ~r2_hidden(D_6, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_232, c_4])).
% 3.78/1.66  tff(c_1469, plain, (![A_121]: (~r2_hidden('#skF_3'(A_121), '#skF_7') | ~m1_subset_1(A_121, k1_zfmisc_1(k3_subset_1('#skF_6', '#skF_7'))) | k1_xboole_0=A_121)), inference(resolution, [status(thm)], [c_671, c_236])).
% 3.78/1.66  tff(c_2272, plain, (![C_170]: (~r2_hidden('#skF_3'(C_170), '#skF_7') | k1_xboole_0=C_170 | ~r1_tarski(C_170, k3_subset_1('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_179, c_1469])).
% 3.78/1.66  tff(c_2298, plain, (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_20, c_2272])).
% 3.78/1.66  tff(c_2310, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2298])).
% 3.78/1.66  tff(c_2312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_2310])).
% 3.78/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.66  
% 3.78/1.66  Inference rules
% 3.78/1.66  ----------------------
% 3.78/1.66  #Ref     : 0
% 3.78/1.66  #Sup     : 480
% 3.78/1.66  #Fact    : 0
% 3.78/1.66  #Define  : 0
% 3.78/1.66  #Split   : 8
% 3.78/1.66  #Chain   : 0
% 3.78/1.66  #Close   : 0
% 3.78/1.66  
% 3.78/1.66  Ordering : KBO
% 3.78/1.66  
% 3.78/1.66  Simplification rules
% 3.78/1.66  ----------------------
% 3.78/1.66  #Subsume      : 66
% 3.78/1.66  #Demod        : 114
% 3.78/1.66  #Tautology    : 115
% 3.78/1.66  #SimpNegUnit  : 50
% 3.78/1.66  #BackRed      : 11
% 3.78/1.66  
% 3.78/1.66  #Partial instantiations: 0
% 3.78/1.66  #Strategies tried      : 1
% 3.78/1.66  
% 3.78/1.66  Timing (in seconds)
% 3.78/1.66  ----------------------
% 3.78/1.66  Preprocessing        : 0.31
% 3.78/1.66  Parsing              : 0.16
% 3.78/1.66  CNF conversion       : 0.02
% 3.78/1.66  Main loop            : 0.59
% 3.78/1.66  Inferencing          : 0.20
% 3.78/1.66  Reduction            : 0.17
% 3.78/1.66  Demodulation         : 0.12
% 3.78/1.66  BG Simplification    : 0.03
% 3.78/1.66  Subsumption          : 0.13
% 3.78/1.66  Abstraction          : 0.03
% 3.78/1.66  MUC search           : 0.00
% 3.78/1.66  Cooper               : 0.00
% 3.78/1.66  Total                : 0.93
% 3.78/1.66  Index Insertion      : 0.00
% 3.78/1.66  Index Deletion       : 0.00
% 3.78/1.66  Index Matching       : 0.00
% 3.78/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
