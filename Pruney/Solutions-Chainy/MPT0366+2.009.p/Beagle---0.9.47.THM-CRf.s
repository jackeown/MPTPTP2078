%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:45 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   52 (  57 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 (  94 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( ( r1_tarski(B,C)
                    & r1_xboole_0(D,C) )
                 => r1_tarski(B,k3_subset_1(A,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_68,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(A_34,B_35) = B_35
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_86,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(k2_xboole_0(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_90,plain,(
    ! [C_43] :
      ( r1_tarski('#skF_3',C_43)
      | ~ r1_tarski('#skF_4',C_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_86])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_98,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_5')) ),
    inference(resolution,[status(thm)],[c_90,c_24])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_433,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k3_subset_1(A_77,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_443,plain,(
    k4_xboole_0('#skF_2','#skF_5') = k3_subset_1('#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_433])).

tff(c_26,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_35,plain,(
    ! [B_28,A_29] :
      ( r1_xboole_0(B_28,A_29)
      | ~ r1_xboole_0(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_38,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_35])).

tff(c_43,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = A_30
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_43])).

tff(c_466,plain,(
    ! [A_79,C_80,B_81] :
      ( r1_tarski(k4_xboole_0(A_79,C_80),k4_xboole_0(B_81,C_80))
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_829,plain,(
    ! [B_108] :
      ( r1_tarski('#skF_4',k4_xboole_0(B_108,'#skF_5'))
      | ~ r1_tarski('#skF_4',B_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_466])).

tff(c_838,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_5'))
    | ~ r1_tarski('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_829])).

tff(c_844,plain,(
    ~ r1_tarski('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_838])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_428,plain,(
    ! [C_74,A_75,B_76] :
      ( r2_hidden(C_74,A_75)
      | ~ r2_hidden(C_74,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_868,plain,(
    ! [A_109,B_110,A_111] :
      ( r2_hidden('#skF_1'(A_109,B_110),A_111)
      | ~ m1_subset_1(A_109,k1_zfmisc_1(A_111))
      | r1_tarski(A_109,B_110) ) ),
    inference(resolution,[status(thm)],[c_6,c_428])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_880,plain,(
    ! [A_112,A_113] :
      ( ~ m1_subset_1(A_112,k1_zfmisc_1(A_113))
      | r1_tarski(A_112,A_113) ) ),
    inference(resolution,[status(thm)],[c_868,c_4])).

tff(c_889,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_880])).

tff(c_896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:43:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.46  
% 2.83/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.46  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.83/1.46  
% 2.83/1.46  %Foreground sorts:
% 2.83/1.46  
% 2.83/1.46  
% 2.83/1.46  %Background operators:
% 2.83/1.46  
% 2.83/1.46  
% 2.83/1.46  %Foreground operators:
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.46  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.83/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.83/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.83/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.46  
% 3.02/1.47  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 3.02/1.47  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.02/1.47  tff(f_40, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.02/1.47  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.02/1.47  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.02/1.47  tff(f_52, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.02/1.47  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_xboole_1)).
% 3.02/1.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.02/1.47  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.02/1.47  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.02/1.47  tff(c_68, plain, (![A_34, B_35]: (k2_xboole_0(A_34, B_35)=B_35 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.02/1.47  tff(c_72, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_28, c_68])).
% 3.02/1.47  tff(c_86, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(k2_xboole_0(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.02/1.47  tff(c_90, plain, (![C_43]: (r1_tarski('#skF_3', C_43) | ~r1_tarski('#skF_4', C_43))), inference(superposition, [status(thm), theory('equality')], [c_72, c_86])).
% 3.02/1.47  tff(c_24, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.02/1.47  tff(c_98, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_5'))), inference(resolution, [status(thm)], [c_90, c_24])).
% 3.02/1.47  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.02/1.47  tff(c_433, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k3_subset_1(A_77, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.02/1.47  tff(c_443, plain, (k4_xboole_0('#skF_2', '#skF_5')=k3_subset_1('#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_30, c_433])).
% 3.02/1.47  tff(c_26, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.02/1.47  tff(c_35, plain, (![B_28, A_29]: (r1_xboole_0(B_28, A_29) | ~r1_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.02/1.47  tff(c_38, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_35])).
% 3.02/1.47  tff(c_43, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=A_30 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.02/1.47  tff(c_50, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_43])).
% 3.02/1.47  tff(c_466, plain, (![A_79, C_80, B_81]: (r1_tarski(k4_xboole_0(A_79, C_80), k4_xboole_0(B_81, C_80)) | ~r1_tarski(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.02/1.47  tff(c_829, plain, (![B_108]: (r1_tarski('#skF_4', k4_xboole_0(B_108, '#skF_5')) | ~r1_tarski('#skF_4', B_108))), inference(superposition, [status(thm), theory('equality')], [c_50, c_466])).
% 3.02/1.47  tff(c_838, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_5')) | ~r1_tarski('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_443, c_829])).
% 3.02/1.47  tff(c_844, plain, (~r1_tarski('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_98, c_838])).
% 3.02/1.47  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.02/1.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.02/1.47  tff(c_428, plain, (![C_74, A_75, B_76]: (r2_hidden(C_74, A_75) | ~r2_hidden(C_74, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.02/1.47  tff(c_868, plain, (![A_109, B_110, A_111]: (r2_hidden('#skF_1'(A_109, B_110), A_111) | ~m1_subset_1(A_109, k1_zfmisc_1(A_111)) | r1_tarski(A_109, B_110))), inference(resolution, [status(thm)], [c_6, c_428])).
% 3.02/1.47  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.02/1.47  tff(c_880, plain, (![A_112, A_113]: (~m1_subset_1(A_112, k1_zfmisc_1(A_113)) | r1_tarski(A_112, A_113))), inference(resolution, [status(thm)], [c_868, c_4])).
% 3.02/1.47  tff(c_889, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_880])).
% 3.02/1.47  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_844, c_889])).
% 3.02/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.47  
% 3.02/1.47  Inference rules
% 3.02/1.47  ----------------------
% 3.02/1.47  #Ref     : 0
% 3.02/1.47  #Sup     : 206
% 3.02/1.47  #Fact    : 0
% 3.02/1.47  #Define  : 0
% 3.02/1.47  #Split   : 9
% 3.02/1.47  #Chain   : 0
% 3.02/1.47  #Close   : 0
% 3.02/1.47  
% 3.02/1.47  Ordering : KBO
% 3.02/1.47  
% 3.02/1.47  Simplification rules
% 3.02/1.47  ----------------------
% 3.02/1.47  #Subsume      : 10
% 3.02/1.47  #Demod        : 85
% 3.02/1.47  #Tautology    : 97
% 3.02/1.47  #SimpNegUnit  : 5
% 3.02/1.47  #BackRed      : 0
% 3.02/1.47  
% 3.02/1.47  #Partial instantiations: 0
% 3.02/1.47  #Strategies tried      : 1
% 3.02/1.47  
% 3.02/1.47  Timing (in seconds)
% 3.02/1.47  ----------------------
% 3.02/1.48  Preprocessing        : 0.29
% 3.02/1.48  Parsing              : 0.15
% 3.02/1.48  CNF conversion       : 0.02
% 3.02/1.48  Main loop            : 0.37
% 3.02/1.48  Inferencing          : 0.14
% 3.02/1.48  Reduction            : 0.12
% 3.02/1.48  Demodulation         : 0.08
% 3.02/1.48  BG Simplification    : 0.02
% 3.02/1.48  Subsumption          : 0.07
% 3.02/1.48  Abstraction          : 0.02
% 3.02/1.48  MUC search           : 0.00
% 3.02/1.48  Cooper               : 0.00
% 3.02/1.48  Total                : 0.69
% 3.02/1.48  Index Insertion      : 0.00
% 3.02/1.48  Index Deletion       : 0.00
% 3.02/1.48  Index Matching       : 0.00
% 3.02/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
