%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:52 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   65 (  80 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :   84 ( 145 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_70,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_50,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

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

tff(c_46,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_100,plain,(
    ! [B_32,A_33] :
      ( v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_108,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_100])).

tff(c_109,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( r2_hidden(B_15,A_14)
      | ~ m1_subset_1(B_15,A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_40,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_211,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k3_subset_1(A_46,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_220,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_211])).

tff(c_36,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_131,plain,(
    ! [B_40,A_41] :
      ( r2_hidden(B_40,A_41)
      | ~ m1_subset_1(B_40,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_13] : k3_tarski(k1_zfmisc_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_91,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,k3_tarski(B_29))
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_94,plain,(
    ! [A_28,A_13] :
      ( r1_tarski(A_28,A_13)
      | ~ r2_hidden(A_28,k1_zfmisc_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_91])).

tff(c_135,plain,(
    ! [B_40,A_13] :
      ( r1_tarski(B_40,A_13)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_131,c_94])).

tff(c_164,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(B_44,A_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_135])).

tff(c_173,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_164])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_177,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_173,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_184,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_2])).

tff(c_18,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_200,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_18])).

tff(c_225,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_200])).

tff(c_486,plain,(
    ! [A_78,C_79,B_80] :
      ( r2_hidden(A_78,C_79)
      | ~ r2_hidden(A_78,B_80)
      | r2_hidden(A_78,k5_xboole_0(B_80,C_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_636,plain,(
    ! [A_94] :
      ( r2_hidden(A_94,'#skF_2')
      | ~ r2_hidden(A_94,'#skF_1')
      | r2_hidden(A_94,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_486])).

tff(c_38,plain,(
    ~ r2_hidden('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_648,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_636,c_38])).

tff(c_656,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_648])).

tff(c_659,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_656])).

tff(c_662,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_659])).

tff(c_664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_662])).

tff(c_666,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_673,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_666,c_4])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:19:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.37  
% 2.59/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.37  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.59/1.37  
% 2.59/1.37  %Foreground sorts:
% 2.59/1.37  
% 2.59/1.37  
% 2.59/1.37  %Background operators:
% 2.59/1.37  
% 2.59/1.37  
% 2.59/1.37  %Foreground operators:
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.59/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.59/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.59/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.59/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.59/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.59/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.37  
% 3.00/1.38  tff(f_85, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 3.00/1.38  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.00/1.38  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.00/1.38  tff(f_70, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.00/1.38  tff(f_50, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.00/1.38  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.00/1.38  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.00/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.00/1.38  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.00/1.38  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.00/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.00/1.38  tff(c_46, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.00/1.38  tff(c_42, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.00/1.38  tff(c_100, plain, (![B_32, A_33]: (v1_xboole_0(B_32) | ~m1_subset_1(B_32, A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.38  tff(c_108, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_100])).
% 3.00/1.38  tff(c_109, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_108])).
% 3.00/1.38  tff(c_28, plain, (![B_15, A_14]: (r2_hidden(B_15, A_14) | ~m1_subset_1(B_15, A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.38  tff(c_40, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.00/1.38  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.00/1.38  tff(c_211, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k3_subset_1(A_46, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.00/1.38  tff(c_220, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_211])).
% 3.00/1.38  tff(c_36, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.00/1.38  tff(c_131, plain, (![B_40, A_41]: (r2_hidden(B_40, A_41) | ~m1_subset_1(B_40, A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.38  tff(c_24, plain, (![A_13]: (k3_tarski(k1_zfmisc_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.00/1.38  tff(c_91, plain, (![A_28, B_29]: (r1_tarski(A_28, k3_tarski(B_29)) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.00/1.38  tff(c_94, plain, (![A_28, A_13]: (r1_tarski(A_28, A_13) | ~r2_hidden(A_28, k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_91])).
% 3.00/1.38  tff(c_135, plain, (![B_40, A_13]: (r1_tarski(B_40, A_13) | ~m1_subset_1(B_40, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_131, c_94])).
% 3.00/1.38  tff(c_164, plain, (![B_44, A_45]: (r1_tarski(B_44, A_45) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)))), inference(negUnitSimplification, [status(thm)], [c_36, c_135])).
% 3.00/1.38  tff(c_173, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_164])).
% 3.00/1.38  tff(c_20, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.00/1.38  tff(c_177, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_173, c_20])).
% 3.00/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.38  tff(c_184, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_177, c_2])).
% 3.00/1.38  tff(c_18, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.00/1.38  tff(c_200, plain, (k5_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_184, c_18])).
% 3.00/1.38  tff(c_225, plain, (k5_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_220, c_200])).
% 3.00/1.38  tff(c_486, plain, (![A_78, C_79, B_80]: (r2_hidden(A_78, C_79) | ~r2_hidden(A_78, B_80) | r2_hidden(A_78, k5_xboole_0(B_80, C_79)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.00/1.38  tff(c_636, plain, (![A_94]: (r2_hidden(A_94, '#skF_2') | ~r2_hidden(A_94, '#skF_1') | r2_hidden(A_94, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_225, c_486])).
% 3.00/1.38  tff(c_38, plain, (~r2_hidden('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.00/1.38  tff(c_648, plain, (r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_636, c_38])).
% 3.00/1.38  tff(c_656, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_40, c_648])).
% 3.00/1.38  tff(c_659, plain, (~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_656])).
% 3.00/1.38  tff(c_662, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_659])).
% 3.00/1.38  tff(c_664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_662])).
% 3.00/1.38  tff(c_666, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_108])).
% 3.00/1.38  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.00/1.38  tff(c_673, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_666, c_4])).
% 3.00/1.38  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_673])).
% 3.00/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.38  
% 3.00/1.38  Inference rules
% 3.00/1.38  ----------------------
% 3.00/1.38  #Ref     : 0
% 3.00/1.38  #Sup     : 150
% 3.00/1.38  #Fact    : 0
% 3.00/1.38  #Define  : 0
% 3.00/1.38  #Split   : 5
% 3.00/1.38  #Chain   : 0
% 3.00/1.38  #Close   : 0
% 3.00/1.38  
% 3.00/1.38  Ordering : KBO
% 3.00/1.38  
% 3.00/1.38  Simplification rules
% 3.00/1.38  ----------------------
% 3.00/1.38  #Subsume      : 18
% 3.00/1.38  #Demod        : 18
% 3.00/1.38  #Tautology    : 62
% 3.00/1.38  #SimpNegUnit  : 12
% 3.00/1.38  #BackRed      : 0
% 3.00/1.38  
% 3.00/1.38  #Partial instantiations: 0
% 3.00/1.38  #Strategies tried      : 1
% 3.00/1.38  
% 3.00/1.38  Timing (in seconds)
% 3.00/1.38  ----------------------
% 3.00/1.39  Preprocessing        : 0.30
% 3.00/1.39  Parsing              : 0.15
% 3.00/1.39  CNF conversion       : 0.02
% 3.00/1.39  Main loop            : 0.34
% 3.00/1.39  Inferencing          : 0.13
% 3.00/1.39  Reduction            : 0.10
% 3.00/1.39  Demodulation         : 0.07
% 3.00/1.39  BG Simplification    : 0.02
% 3.00/1.39  Subsumption          : 0.06
% 3.00/1.39  Abstraction          : 0.02
% 3.00/1.39  MUC search           : 0.00
% 3.00/1.39  Cooper               : 0.00
% 3.00/1.39  Total                : 0.67
% 3.00/1.39  Index Insertion      : 0.00
% 3.00/1.39  Index Deletion       : 0.00
% 3.00/1.39  Index Matching       : 0.00
% 3.00/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
