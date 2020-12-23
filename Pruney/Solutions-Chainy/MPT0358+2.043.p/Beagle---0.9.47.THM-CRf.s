%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:05 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 102 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 148 expanded)
%              Number of equality atoms :   23 (  60 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_74,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_52,axiom,(
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

tff(c_42,plain,(
    ! [A_24] : k1_subset_1(A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_48,plain,
    ( k1_subset_1('#skF_5') != '#skF_6'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_55,plain,
    ( k1_xboole_0 != '#skF_6'
    | ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_48])).

tff(c_103,plain,(
    ~ r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_54,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_subset_1('#skF_5') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_56,plain,
    ( r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54])).

tff(c_104,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_38,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_107,plain,(
    ! [A_20] : r1_tarski('#skF_6',A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_38])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_103])).

tff(c_145,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_145])).

tff(c_148,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_32,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_150,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_150])).

tff(c_152,plain,(
    r1_tarski('#skF_6',k3_subset_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_157,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_152,c_36])).

tff(c_191,plain,(
    ! [D_43,B_44,A_45] :
      ( r2_hidden(D_43,B_44)
      | ~ r2_hidden(D_43,k3_xboole_0(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_198,plain,(
    ! [D_43] :
      ( r2_hidden(D_43,k3_subset_1('#skF_5','#skF_6'))
      | ~ r2_hidden(D_43,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_191])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_429,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_433,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_429])).

tff(c_40,plain,(
    ! [A_21,C_23,B_22] :
      ( r1_xboole_0(A_21,k4_xboole_0(C_23,B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_460,plain,(
    ! [A_79] :
      ( r1_xboole_0(A_79,k3_subset_1('#skF_5','#skF_6'))
      | ~ r1_tarski(A_79,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_40])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_541,plain,(
    ! [C_86,A_87] :
      ( ~ r2_hidden(C_86,k3_subset_1('#skF_5','#skF_6'))
      | ~ r2_hidden(C_86,A_87)
      | ~ r1_tarski(A_87,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_460,c_20])).

tff(c_678,plain,(
    ! [D_99,A_100] :
      ( ~ r2_hidden(D_99,A_100)
      | ~ r1_tarski(A_100,'#skF_6')
      | ~ r2_hidden(D_99,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_198,c_541])).

tff(c_872,plain,(
    ! [A_111] :
      ( ~ r1_tarski(A_111,'#skF_6')
      | ~ r2_hidden('#skF_4'(A_111),'#skF_6')
      | k1_xboole_0 = A_111 ) ),
    inference(resolution,[status(thm)],[c_26,c_678])).

tff(c_876,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_26,c_872])).

tff(c_879,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_876])).

tff(c_881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.42  
% 2.85/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.85/1.43  
% 2.85/1.43  %Foreground sorts:
% 2.85/1.43  
% 2.85/1.43  
% 2.85/1.43  %Background operators:
% 2.85/1.43  
% 2.85/1.43  
% 2.85/1.43  %Foreground operators:
% 2.85/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.85/1.43  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.85/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.85/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.85/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.85/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.85/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.85/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.85/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.85/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.43  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.85/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.85/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.43  
% 2.85/1.44  tff(f_80, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.85/1.44  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.85/1.44  tff(f_74, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.85/1.44  tff(f_66, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.85/1.44  tff(f_60, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.85/1.44  tff(f_72, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.85/1.44  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.85/1.44  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.85/1.44  tff(f_78, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.85/1.44  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.85/1.44  tff(c_42, plain, (![A_24]: (k1_subset_1(A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.85/1.44  tff(c_48, plain, (k1_subset_1('#skF_5')!='#skF_6' | ~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.85/1.44  tff(c_55, plain, (k1_xboole_0!='#skF_6' | ~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_48])).
% 2.85/1.44  tff(c_103, plain, (~r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_55])).
% 2.85/1.44  tff(c_54, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_subset_1('#skF_5')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.85/1.44  tff(c_56, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6')) | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_54])).
% 2.85/1.44  tff(c_104, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_56])).
% 2.85/1.44  tff(c_38, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.85/1.44  tff(c_107, plain, (![A_20]: (r1_tarski('#skF_6', A_20))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_38])).
% 2.85/1.44  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_107, c_103])).
% 2.85/1.44  tff(c_145, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_56])).
% 2.85/1.44  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_145])).
% 2.85/1.44  tff(c_148, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_55])).
% 2.85/1.44  tff(c_32, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.85/1.44  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.85/1.44  tff(c_150, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_56])).
% 2.85/1.44  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_150])).
% 2.85/1.44  tff(c_152, plain, (r1_tarski('#skF_6', k3_subset_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_56])).
% 2.85/1.44  tff(c_36, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.85/1.44  tff(c_157, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_152, c_36])).
% 2.85/1.44  tff(c_191, plain, (![D_43, B_44, A_45]: (r2_hidden(D_43, B_44) | ~r2_hidden(D_43, k3_xboole_0(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.85/1.44  tff(c_198, plain, (![D_43]: (r2_hidden(D_43, k3_subset_1('#skF_5', '#skF_6')) | ~r2_hidden(D_43, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_191])).
% 2.85/1.44  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.85/1.44  tff(c_429, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.85/1.44  tff(c_433, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_429])).
% 2.85/1.44  tff(c_40, plain, (![A_21, C_23, B_22]: (r1_xboole_0(A_21, k4_xboole_0(C_23, B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.85/1.44  tff(c_460, plain, (![A_79]: (r1_xboole_0(A_79, k3_subset_1('#skF_5', '#skF_6')) | ~r1_tarski(A_79, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_433, c_40])).
% 2.85/1.44  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.85/1.44  tff(c_541, plain, (![C_86, A_87]: (~r2_hidden(C_86, k3_subset_1('#skF_5', '#skF_6')) | ~r2_hidden(C_86, A_87) | ~r1_tarski(A_87, '#skF_6'))), inference(resolution, [status(thm)], [c_460, c_20])).
% 2.85/1.44  tff(c_678, plain, (![D_99, A_100]: (~r2_hidden(D_99, A_100) | ~r1_tarski(A_100, '#skF_6') | ~r2_hidden(D_99, '#skF_6'))), inference(resolution, [status(thm)], [c_198, c_541])).
% 2.85/1.44  tff(c_872, plain, (![A_111]: (~r1_tarski(A_111, '#skF_6') | ~r2_hidden('#skF_4'(A_111), '#skF_6') | k1_xboole_0=A_111)), inference(resolution, [status(thm)], [c_26, c_678])).
% 2.85/1.44  tff(c_876, plain, (~r1_tarski('#skF_6', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_26, c_872])).
% 2.85/1.44  tff(c_879, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_876])).
% 2.85/1.44  tff(c_881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_879])).
% 2.85/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.44  
% 2.85/1.44  Inference rules
% 2.85/1.44  ----------------------
% 2.85/1.44  #Ref     : 0
% 2.85/1.44  #Sup     : 199
% 2.85/1.44  #Fact    : 0
% 2.85/1.44  #Define  : 0
% 2.85/1.44  #Split   : 4
% 2.85/1.44  #Chain   : 0
% 2.85/1.44  #Close   : 0
% 2.85/1.44  
% 2.85/1.44  Ordering : KBO
% 2.85/1.44  
% 2.85/1.44  Simplification rules
% 2.85/1.44  ----------------------
% 2.85/1.44  #Subsume      : 44
% 2.85/1.44  #Demod        : 61
% 2.85/1.44  #Tautology    : 83
% 2.85/1.44  #SimpNegUnit  : 3
% 2.85/1.44  #BackRed      : 4
% 2.85/1.44  
% 2.85/1.44  #Partial instantiations: 0
% 2.85/1.44  #Strategies tried      : 1
% 2.85/1.44  
% 2.85/1.44  Timing (in seconds)
% 2.85/1.44  ----------------------
% 2.85/1.44  Preprocessing        : 0.32
% 2.85/1.44  Parsing              : 0.16
% 2.85/1.44  CNF conversion       : 0.02
% 2.85/1.44  Main loop            : 0.36
% 2.85/1.44  Inferencing          : 0.13
% 2.85/1.44  Reduction            : 0.11
% 2.85/1.44  Demodulation         : 0.08
% 2.85/1.44  BG Simplification    : 0.02
% 2.85/1.44  Subsumption          : 0.07
% 2.85/1.44  Abstraction          : 0.02
% 2.85/1.44  MUC search           : 0.00
% 2.85/1.45  Cooper               : 0.00
% 2.85/1.45  Total                : 0.71
% 2.85/1.45  Index Insertion      : 0.00
% 2.85/1.45  Index Deletion       : 0.00
% 3.12/1.45  Index Matching       : 0.00
% 3.12/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
