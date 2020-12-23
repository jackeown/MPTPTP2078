%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:24 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   56 (  60 expanded)
%              Number of leaves         :   33 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 (  85 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] : ~ v1_xboole_0(k1_enumset1(A,B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_24,B_25,C_26] : ~ v1_xboole_0(k1_enumset1(A_24,B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_71,plain,(
    ! [A_41,B_42] : ~ v1_xboole_0(k2_tarski(A_41,B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_22])).

tff(c_73,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_71])).

tff(c_20,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(k1_tarski(A_22),B_23)
      | r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_99,plain,(
    ! [A_54,B_55] :
      ( ~ r1_xboole_0(A_54,B_55)
      | v1_xboole_0(k3_xboole_0(A_54,B_55)) ) ),
    inference(resolution,[status(thm)],[c_4,c_76])).

tff(c_103,plain,(
    ! [A_56] :
      ( ~ r1_xboole_0(A_56,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_99])).

tff(c_107,plain,(
    ! [A_22] :
      ( v1_xboole_0(k1_tarski(A_22))
      | r2_hidden(A_22,k1_tarski(A_22)) ) ),
    inference(resolution,[status(thm)],[c_20,c_103])).

tff(c_110,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_107])).

tff(c_180,plain,(
    ! [D_70,C_71,B_72,A_73] :
      ( r2_hidden(k1_funct_1(D_70,C_71),B_72)
      | k1_xboole_0 = B_72
      | ~ r2_hidden(C_71,A_73)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72)))
      | ~ v1_funct_2(D_70,A_73,B_72)
      | ~ v1_funct_1(D_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_193,plain,(
    ! [D_74,A_75,B_76] :
      ( r2_hidden(k1_funct_1(D_74,A_75),B_76)
      | k1_xboole_0 = B_76
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_75),B_76)))
      | ~ v1_funct_2(D_74,k1_tarski(A_75),B_76)
      | ~ v1_funct_1(D_74) ) ),
    inference(resolution,[status(thm)],[c_110,c_180])).

tff(c_196,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_193])).

tff(c_199,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_196])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:43:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.23  
% 2.05/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.23  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.05/1.23  
% 2.05/1.23  %Foreground sorts:
% 2.05/1.23  
% 2.05/1.23  
% 2.05/1.23  %Background operators:
% 2.05/1.23  
% 2.05/1.23  
% 2.05/1.23  %Foreground operators:
% 2.05/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.05/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.05/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.05/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.05/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.05/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.23  
% 2.17/1.24  tff(f_87, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.17/1.24  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.17/1.24  tff(f_51, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.17/1.24  tff(f_63, axiom, (![A, B, C]: ~v1_xboole_0(k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_subset_1)).
% 2.17/1.24  tff(f_60, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.17/1.24  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.17/1.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.17/1.24  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.17/1.24  tff(f_75, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.17/1.24  tff(c_28, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.17/1.24  tff(c_26, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.17/1.24  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.17/1.24  tff(c_32, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.17/1.24  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.17/1.24  tff(c_12, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.24  tff(c_60, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.24  tff(c_22, plain, (![A_24, B_25, C_26]: (~v1_xboole_0(k1_enumset1(A_24, B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.17/1.24  tff(c_71, plain, (![A_41, B_42]: (~v1_xboole_0(k2_tarski(A_41, B_42)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_22])).
% 2.17/1.24  tff(c_73, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_71])).
% 2.17/1.24  tff(c_20, plain, (![A_22, B_23]: (r1_xboole_0(k1_tarski(A_22), B_23) | r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.17/1.24  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.24  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.24  tff(c_76, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.24  tff(c_99, plain, (![A_54, B_55]: (~r1_xboole_0(A_54, B_55) | v1_xboole_0(k3_xboole_0(A_54, B_55)))), inference(resolution, [status(thm)], [c_4, c_76])).
% 2.17/1.24  tff(c_103, plain, (![A_56]: (~r1_xboole_0(A_56, A_56) | v1_xboole_0(A_56))), inference(superposition, [status(thm), theory('equality')], [c_6, c_99])).
% 2.17/1.24  tff(c_107, plain, (![A_22]: (v1_xboole_0(k1_tarski(A_22)) | r2_hidden(A_22, k1_tarski(A_22)))), inference(resolution, [status(thm)], [c_20, c_103])).
% 2.17/1.24  tff(c_110, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(negUnitSimplification, [status(thm)], [c_73, c_107])).
% 2.17/1.24  tff(c_180, plain, (![D_70, C_71, B_72, A_73]: (r2_hidden(k1_funct_1(D_70, C_71), B_72) | k1_xboole_0=B_72 | ~r2_hidden(C_71, A_73) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))) | ~v1_funct_2(D_70, A_73, B_72) | ~v1_funct_1(D_70))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.17/1.24  tff(c_193, plain, (![D_74, A_75, B_76]: (r2_hidden(k1_funct_1(D_74, A_75), B_76) | k1_xboole_0=B_76 | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_75), B_76))) | ~v1_funct_2(D_74, k1_tarski(A_75), B_76) | ~v1_funct_1(D_74))), inference(resolution, [status(thm)], [c_110, c_180])).
% 2.17/1.24  tff(c_196, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_193])).
% 2.17/1.24  tff(c_199, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_196])).
% 2.17/1.24  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_199])).
% 2.17/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  Inference rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Ref     : 0
% 2.17/1.24  #Sup     : 37
% 2.17/1.24  #Fact    : 0
% 2.17/1.24  #Define  : 0
% 2.17/1.24  #Split   : 0
% 2.17/1.24  #Chain   : 0
% 2.17/1.24  #Close   : 0
% 2.17/1.24  
% 2.17/1.24  Ordering : KBO
% 2.17/1.24  
% 2.17/1.24  Simplification rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Subsume      : 5
% 2.17/1.24  #Demod        : 5
% 2.17/1.24  #Tautology    : 17
% 2.17/1.24  #SimpNegUnit  : 2
% 2.17/1.24  #BackRed      : 0
% 2.17/1.24  
% 2.17/1.24  #Partial instantiations: 0
% 2.17/1.24  #Strategies tried      : 1
% 2.17/1.24  
% 2.17/1.24  Timing (in seconds)
% 2.17/1.24  ----------------------
% 2.17/1.24  Preprocessing        : 0.32
% 2.17/1.25  Parsing              : 0.17
% 2.17/1.25  CNF conversion       : 0.02
% 2.17/1.25  Main loop            : 0.17
% 2.17/1.25  Inferencing          : 0.07
% 2.17/1.25  Reduction            : 0.05
% 2.17/1.25  Demodulation         : 0.03
% 2.17/1.25  BG Simplification    : 0.01
% 2.17/1.25  Subsumption          : 0.02
% 2.17/1.25  Abstraction          : 0.01
% 2.17/1.25  MUC search           : 0.00
% 2.17/1.25  Cooper               : 0.00
% 2.17/1.25  Total                : 0.51
% 2.17/1.25  Index Insertion      : 0.00
% 2.17/1.25  Index Deletion       : 0.00
% 2.17/1.25  Index Matching       : 0.00
% 2.17/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
