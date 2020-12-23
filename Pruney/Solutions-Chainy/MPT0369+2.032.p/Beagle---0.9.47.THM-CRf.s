%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:55 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 153 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_45,plain,(
    ! [B_24,A_25] :
      ( v1_xboole_0(B_24)
      | ~ m1_subset_1(B_24,A_25)
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_45])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_22,plain,(
    ! [B_10,A_9] :
      ( r2_hidden(B_10,A_9)
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_118,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k3_subset_1(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_127,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_118])).

tff(c_18,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_135,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_18])).

tff(c_110,plain,(
    ! [A_34,B_35] :
      ( k3_subset_1(A_34,k3_subset_1(A_34,B_35)) = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_117,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_110])).

tff(c_153,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k3_subset_1(A_38,B_39),k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_532,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(A_88,k3_subset_1(A_88,B_89)) = k3_subset_1(A_88,k3_subset_1(A_88,B_89))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_153,c_28])).

tff(c_539,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_532])).

tff(c_543,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_117,c_539])).

tff(c_16,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_208,plain,(
    ! [A_48,C_49,B_50] :
      ( r2_hidden(A_48,C_49)
      | ~ r2_hidden(A_48,B_50)
      | r2_hidden(A_48,k5_xboole_0(B_50,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_365,plain,(
    ! [A_69,A_70,B_71] :
      ( r2_hidden(A_69,k3_xboole_0(A_70,B_71))
      | ~ r2_hidden(A_69,A_70)
      | r2_hidden(A_69,k4_xboole_0(A_70,B_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_208])).

tff(c_389,plain,(
    ! [A_69] :
      ( r2_hidden(A_69,k3_xboole_0('#skF_1','#skF_2'))
      | ~ r2_hidden(A_69,'#skF_1')
      | r2_hidden(A_69,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_365])).

tff(c_717,plain,(
    ! [A_95] :
      ( r2_hidden(A_95,'#skF_2')
      | ~ r2_hidden(A_95,'#skF_1')
      | r2_hidden(A_95,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_543,c_389])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_729,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_717,c_34])).

tff(c_737,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_729])).

tff(c_740,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_737])).

tff(c_743,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_740])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_743])).

tff(c_747,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_754,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_747,c_2])).

tff(c_758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_754])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:38:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.69/1.40  
% 2.69/1.40  %Foreground sorts:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Background operators:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Foreground operators:
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.69/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.69/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.40  
% 2.69/1.41  tff(f_80, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.69/1.41  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.69/1.41  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.69/1.41  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.69/1.41  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.69/1.41  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.69/1.41  tff(f_38, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.69/1.41  tff(f_36, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.69/1.41  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.69/1.41  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.69/1.41  tff(c_38, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.69/1.41  tff(c_45, plain, (![B_24, A_25]: (v1_xboole_0(B_24) | ~m1_subset_1(B_24, A_25) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.69/1.41  tff(c_57, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_45])).
% 2.69/1.41  tff(c_58, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_57])).
% 2.69/1.41  tff(c_22, plain, (![B_10, A_9]: (r2_hidden(B_10, A_9) | ~m1_subset_1(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.69/1.41  tff(c_36, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.69/1.41  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.69/1.41  tff(c_118, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k3_subset_1(A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.41  tff(c_127, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_118])).
% 2.69/1.41  tff(c_18, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.69/1.41  tff(c_135, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_127, c_18])).
% 2.69/1.41  tff(c_110, plain, (![A_34, B_35]: (k3_subset_1(A_34, k3_subset_1(A_34, B_35))=B_35 | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.69/1.41  tff(c_117, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_40, c_110])).
% 2.69/1.41  tff(c_153, plain, (![A_38, B_39]: (m1_subset_1(k3_subset_1(A_38, B_39), k1_zfmisc_1(A_38)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.69/1.41  tff(c_28, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.41  tff(c_532, plain, (![A_88, B_89]: (k4_xboole_0(A_88, k3_subset_1(A_88, B_89))=k3_subset_1(A_88, k3_subset_1(A_88, B_89)) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_153, c_28])).
% 2.69/1.41  tff(c_539, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_532])).
% 2.69/1.41  tff(c_543, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_117, c_539])).
% 2.69/1.41  tff(c_16, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.69/1.41  tff(c_208, plain, (![A_48, C_49, B_50]: (r2_hidden(A_48, C_49) | ~r2_hidden(A_48, B_50) | r2_hidden(A_48, k5_xboole_0(B_50, C_49)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.69/1.41  tff(c_365, plain, (![A_69, A_70, B_71]: (r2_hidden(A_69, k3_xboole_0(A_70, B_71)) | ~r2_hidden(A_69, A_70) | r2_hidden(A_69, k4_xboole_0(A_70, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_208])).
% 2.69/1.41  tff(c_389, plain, (![A_69]: (r2_hidden(A_69, k3_xboole_0('#skF_1', '#skF_2')) | ~r2_hidden(A_69, '#skF_1') | r2_hidden(A_69, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_127, c_365])).
% 2.69/1.41  tff(c_717, plain, (![A_95]: (r2_hidden(A_95, '#skF_2') | ~r2_hidden(A_95, '#skF_1') | r2_hidden(A_95, k3_subset_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_543, c_389])).
% 2.69/1.41  tff(c_34, plain, (~r2_hidden('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.69/1.41  tff(c_729, plain, (r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_717, c_34])).
% 2.69/1.41  tff(c_737, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_729])).
% 2.69/1.41  tff(c_740, plain, (~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_737])).
% 2.69/1.41  tff(c_743, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_740])).
% 2.69/1.41  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_743])).
% 2.69/1.41  tff(c_747, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_57])).
% 2.69/1.41  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.41  tff(c_754, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_747, c_2])).
% 2.69/1.41  tff(c_758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_754])).
% 2.69/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.41  
% 2.69/1.41  Inference rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Ref     : 0
% 2.69/1.41  #Sup     : 184
% 2.69/1.41  #Fact    : 0
% 2.69/1.41  #Define  : 0
% 2.69/1.41  #Split   : 6
% 2.69/1.41  #Chain   : 0
% 2.69/1.41  #Close   : 0
% 2.69/1.41  
% 2.69/1.41  Ordering : KBO
% 2.69/1.41  
% 2.69/1.41  Simplification rules
% 2.69/1.41  ----------------------
% 2.69/1.41  #Subsume      : 12
% 2.69/1.41  #Demod        : 40
% 2.69/1.41  #Tautology    : 69
% 2.69/1.41  #SimpNegUnit  : 11
% 2.69/1.42  #BackRed      : 7
% 2.69/1.42  
% 2.69/1.42  #Partial instantiations: 0
% 2.69/1.42  #Strategies tried      : 1
% 2.69/1.42  
% 2.69/1.42  Timing (in seconds)
% 2.69/1.42  ----------------------
% 2.69/1.42  Preprocessing        : 0.29
% 2.69/1.42  Parsing              : 0.15
% 2.69/1.42  CNF conversion       : 0.02
% 2.69/1.42  Main loop            : 0.37
% 2.69/1.42  Inferencing          : 0.14
% 2.69/1.42  Reduction            : 0.11
% 2.69/1.42  Demodulation         : 0.08
% 2.69/1.42  BG Simplification    : 0.02
% 2.69/1.42  Subsumption          : 0.07
% 2.69/1.42  Abstraction          : 0.02
% 2.69/1.42  MUC search           : 0.00
% 2.69/1.42  Cooper               : 0.00
% 2.69/1.42  Total                : 0.68
% 2.69/1.42  Index Insertion      : 0.00
% 2.69/1.42  Index Deletion       : 0.00
% 2.69/1.42  Index Matching       : 0.00
% 2.69/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
