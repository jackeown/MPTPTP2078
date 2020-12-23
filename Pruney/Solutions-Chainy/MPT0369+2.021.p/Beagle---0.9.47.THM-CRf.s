%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:53 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   69 (  84 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :   86 ( 147 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_48,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_75,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_84,plain,(
    ! [B_37,A_38] :
      ( v1_xboole_0(B_37)
      | ~ m1_subset_1(B_37,A_38)
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_92,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_84])).

tff(c_93,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_40,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_48,plain,(
    ! [A_22] : ~ v1_xboole_0(k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_120,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,A_48)
      | ~ m1_subset_1(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_127,plain,(
    ! [B_47,A_13] :
      ( r1_tarski(B_47,A_13)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_120,c_26])).

tff(c_146,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_127])).

tff(c_159,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_146])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_172,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_159,c_22])).

tff(c_18,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_176,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_18])).

tff(c_179,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_176])).

tff(c_206,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k3_subset_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_219,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_206])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k4_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_225,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),k4_xboole_0('#skF_4','#skF_3')) = k5_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_2])).

tff(c_231,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_179,c_225])).

tff(c_250,plain,(
    ! [A_57,C_58,B_59] :
      ( r2_hidden(A_57,C_58)
      | ~ r2_hidden(A_57,B_59)
      | r2_hidden(A_57,k5_xboole_0(B_59,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_419,plain,(
    ! [A_85] :
      ( r2_hidden(A_85,'#skF_4')
      | ~ r2_hidden(A_85,'#skF_3')
      | r2_hidden(A_85,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_250])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_436,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_419,c_50])).

tff(c_446,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_436])).

tff(c_449,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_446])).

tff(c_452,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_449])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_452])).

tff(c_456,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_463,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_456,c_4])).

tff(c_467,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:51:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.37  
% 2.82/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.37  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.82/1.37  
% 2.82/1.37  %Foreground sorts:
% 2.82/1.37  
% 2.82/1.37  
% 2.82/1.37  %Background operators:
% 2.82/1.37  
% 2.82/1.37  
% 2.82/1.37  %Foreground operators:
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.82/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.82/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.82/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.82/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.37  
% 2.82/1.38  tff(f_90, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 2.82/1.38  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.82/1.38  tff(f_42, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.82/1.38  tff(f_48, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.82/1.38  tff(f_75, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.82/1.38  tff(f_55, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.82/1.38  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.82/1.38  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.82/1.38  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.82/1.38  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.82/1.38  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.82/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.82/1.38  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.38  tff(c_54, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.38  tff(c_84, plain, (![B_37, A_38]: (v1_xboole_0(B_37) | ~m1_subset_1(B_37, A_38) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.82/1.38  tff(c_92, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_84])).
% 2.82/1.38  tff(c_93, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_92])).
% 2.82/1.38  tff(c_40, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.82/1.38  tff(c_52, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.38  tff(c_20, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.82/1.38  tff(c_24, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.82/1.38  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.38  tff(c_48, plain, (![A_22]: (~v1_xboole_0(k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.82/1.38  tff(c_120, plain, (![B_47, A_48]: (r2_hidden(B_47, A_48) | ~m1_subset_1(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.82/1.38  tff(c_26, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.82/1.38  tff(c_127, plain, (![B_47, A_13]: (r1_tarski(B_47, A_13) | ~m1_subset_1(B_47, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_120, c_26])).
% 2.82/1.38  tff(c_146, plain, (![B_49, A_50]: (r1_tarski(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)))), inference(negUnitSimplification, [status(thm)], [c_48, c_127])).
% 2.82/1.38  tff(c_159, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_146])).
% 2.82/1.38  tff(c_22, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.82/1.38  tff(c_172, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_159, c_22])).
% 2.82/1.38  tff(c_18, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.82/1.38  tff(c_176, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_172, c_18])).
% 2.82/1.38  tff(c_179, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_176])).
% 2.82/1.38  tff(c_206, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k3_subset_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.82/1.38  tff(c_219, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_206])).
% 2.82/1.38  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k4_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.38  tff(c_225, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k4_xboole_0('#skF_4', '#skF_3'))=k5_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_219, c_2])).
% 2.82/1.38  tff(c_231, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_179, c_225])).
% 2.82/1.38  tff(c_250, plain, (![A_57, C_58, B_59]: (r2_hidden(A_57, C_58) | ~r2_hidden(A_57, B_59) | r2_hidden(A_57, k5_xboole_0(B_59, C_58)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.82/1.38  tff(c_419, plain, (![A_85]: (r2_hidden(A_85, '#skF_4') | ~r2_hidden(A_85, '#skF_3') | r2_hidden(A_85, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_231, c_250])).
% 2.82/1.38  tff(c_50, plain, (~r2_hidden('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.82/1.38  tff(c_436, plain, (r2_hidden('#skF_5', '#skF_4') | ~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_419, c_50])).
% 2.82/1.38  tff(c_446, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_436])).
% 2.82/1.38  tff(c_449, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_446])).
% 2.82/1.38  tff(c_452, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_449])).
% 2.82/1.38  tff(c_454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_452])).
% 2.82/1.38  tff(c_456, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_92])).
% 2.82/1.38  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.38  tff(c_463, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_456, c_4])).
% 2.82/1.38  tff(c_467, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_463])).
% 2.82/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.39  
% 2.82/1.39  Inference rules
% 2.82/1.39  ----------------------
% 2.82/1.39  #Ref     : 0
% 2.82/1.39  #Sup     : 96
% 2.82/1.39  #Fact    : 0
% 2.82/1.39  #Define  : 0
% 2.82/1.39  #Split   : 6
% 2.82/1.39  #Chain   : 0
% 2.82/1.39  #Close   : 0
% 2.82/1.39  
% 2.82/1.39  Ordering : KBO
% 2.82/1.39  
% 2.82/1.39  Simplification rules
% 2.82/1.39  ----------------------
% 2.82/1.39  #Subsume      : 8
% 2.82/1.39  #Demod        : 13
% 2.82/1.39  #Tautology    : 42
% 2.82/1.39  #SimpNegUnit  : 10
% 2.82/1.39  #BackRed      : 2
% 2.82/1.39  
% 2.82/1.39  #Partial instantiations: 0
% 2.82/1.39  #Strategies tried      : 1
% 2.82/1.39  
% 2.82/1.39  Timing (in seconds)
% 2.82/1.39  ----------------------
% 3.03/1.39  Preprocessing        : 0.32
% 3.03/1.39  Parsing              : 0.16
% 3.03/1.39  CNF conversion       : 0.02
% 3.03/1.39  Main loop            : 0.28
% 3.03/1.39  Inferencing          : 0.10
% 3.03/1.39  Reduction            : 0.08
% 3.03/1.39  Demodulation         : 0.05
% 3.03/1.39  BG Simplification    : 0.02
% 3.03/1.39  Subsumption          : 0.06
% 3.03/1.39  Abstraction          : 0.01
% 3.03/1.39  MUC search           : 0.00
% 3.03/1.39  Cooper               : 0.00
% 3.03/1.39  Total                : 0.64
% 3.03/1.39  Index Insertion      : 0.00
% 3.03/1.39  Index Deletion       : 0.00
% 3.03/1.39  Index Matching       : 0.00
% 3.03/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
