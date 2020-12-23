%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:53 EST 2020

% Result     : Theorem 6.39s
% Output     : CNFRefutation 6.39s
% Verified   : 
% Statistics : Number of formulae       :   55 (  67 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 122 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,(
    m1_subset_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_71,plain,(
    ! [B_31,A_32] :
      ( v1_xboole_0(B_31)
      | ~ m1_subset_1(B_31,A_32)
      | ~ v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_79,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_71])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_42,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_165,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k3_subset_1(A_48,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_179,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_165])).

tff(c_38,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1976,plain,(
    ! [A_253,C_254,B_255] :
      ( r2_hidden(A_253,C_254)
      | ~ r2_hidden(A_253,B_255)
      | r2_hidden(A_253,k5_xboole_0(B_255,C_254)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5945,plain,(
    ! [A_457,A_458,B_459] :
      ( r2_hidden(A_457,k3_xboole_0(A_458,B_459))
      | ~ r2_hidden(A_457,A_458)
      | r2_hidden(A_457,k4_xboole_0(A_458,B_459)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1976])).

tff(c_6396,plain,(
    ! [A_467] :
      ( r2_hidden(A_467,k3_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(A_467,'#skF_5')
      | r2_hidden(A_467,k3_subset_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_5945])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k3_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_7260,plain,(
    ! [A_485] :
      ( r2_hidden(A_485,'#skF_6')
      | ~ r2_hidden(A_485,'#skF_5')
      | r2_hidden(A_485,k3_subset_1('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6396,c_8])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_7',k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7285,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_7260,c_50])).

tff(c_7297,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7285])).

tff(c_7300,plain,
    ( ~ m1_subset_1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_7297])).

tff(c_7303,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_7300])).

tff(c_7305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7303])).

tff(c_7307,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_60,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_4'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_28] :
      ( ~ v1_xboole_0(A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_7314,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7307,c_64])).

tff(c_7318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.39/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.30  
% 6.39/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.30  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 6.39/2.30  
% 6.39/2.30  %Foreground sorts:
% 6.39/2.30  
% 6.39/2.30  
% 6.39/2.30  %Background operators:
% 6.39/2.30  
% 6.39/2.30  
% 6.39/2.30  %Foreground operators:
% 6.39/2.30  tff('#skF_4', type, '#skF_4': $i > $i).
% 6.39/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.39/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.39/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.39/2.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.39/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.39/2.30  tff('#skF_7', type, '#skF_7': $i).
% 6.39/2.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.39/2.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.39/2.30  tff('#skF_5', type, '#skF_5': $i).
% 6.39/2.30  tff('#skF_6', type, '#skF_6': $i).
% 6.39/2.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.39/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.39/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.39/2.30  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.39/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.39/2.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.39/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.39/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.39/2.30  
% 6.39/2.31  tff(f_89, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 6.39/2.31  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.39/2.31  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.39/2.31  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.39/2.31  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.39/2.31  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 6.39/2.31  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.39/2.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.39/2.31  tff(c_58, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.39/2.31  tff(c_54, plain, (m1_subset_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.39/2.31  tff(c_71, plain, (![B_31, A_32]: (v1_xboole_0(B_31) | ~m1_subset_1(B_31, A_32) | ~v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.39/2.31  tff(c_79, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_71])).
% 6.39/2.31  tff(c_80, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_79])).
% 6.39/2.31  tff(c_42, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.39/2.31  tff(c_52, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.39/2.31  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.39/2.31  tff(c_165, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=k3_subset_1(A_48, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.39/2.31  tff(c_179, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_165])).
% 6.39/2.31  tff(c_38, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.39/2.31  tff(c_1976, plain, (![A_253, C_254, B_255]: (r2_hidden(A_253, C_254) | ~r2_hidden(A_253, B_255) | r2_hidden(A_253, k5_xboole_0(B_255, C_254)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.39/2.31  tff(c_5945, plain, (![A_457, A_458, B_459]: (r2_hidden(A_457, k3_xboole_0(A_458, B_459)) | ~r2_hidden(A_457, A_458) | r2_hidden(A_457, k4_xboole_0(A_458, B_459)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1976])).
% 6.39/2.31  tff(c_6396, plain, (![A_467]: (r2_hidden(A_467, k3_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(A_467, '#skF_5') | r2_hidden(A_467, k3_subset_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_179, c_5945])).
% 6.39/2.31  tff(c_8, plain, (![D_10, B_6, A_5]: (r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k3_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.39/2.31  tff(c_7260, plain, (![A_485]: (r2_hidden(A_485, '#skF_6') | ~r2_hidden(A_485, '#skF_5') | r2_hidden(A_485, k3_subset_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_6396, c_8])).
% 6.39/2.31  tff(c_50, plain, (~r2_hidden('#skF_7', k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.39/2.31  tff(c_7285, plain, (r2_hidden('#skF_7', '#skF_6') | ~r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_7260, c_50])).
% 6.39/2.31  tff(c_7297, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_7285])).
% 6.39/2.31  tff(c_7300, plain, (~m1_subset_1('#skF_7', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_7297])).
% 6.39/2.31  tff(c_7303, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_7300])).
% 6.39/2.31  tff(c_7305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_7303])).
% 6.39/2.31  tff(c_7307, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_79])).
% 6.39/2.31  tff(c_60, plain, (![A_28]: (r2_hidden('#skF_4'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.39/2.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.39/2.31  tff(c_64, plain, (![A_28]: (~v1_xboole_0(A_28) | k1_xboole_0=A_28)), inference(resolution, [status(thm)], [c_60, c_2])).
% 6.39/2.31  tff(c_7314, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_7307, c_64])).
% 6.39/2.31  tff(c_7318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_7314])).
% 6.39/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.31  
% 6.39/2.31  Inference rules
% 6.39/2.31  ----------------------
% 6.39/2.31  #Ref     : 0
% 6.39/2.31  #Sup     : 1712
% 6.39/2.31  #Fact    : 2
% 6.39/2.31  #Define  : 0
% 6.39/2.31  #Split   : 7
% 6.39/2.31  #Chain   : 0
% 6.39/2.31  #Close   : 0
% 6.39/2.31  
% 6.39/2.31  Ordering : KBO
% 6.39/2.31  
% 6.39/2.31  Simplification rules
% 6.39/2.31  ----------------------
% 6.39/2.31  #Subsume      : 520
% 6.39/2.31  #Demod        : 416
% 6.39/2.31  #Tautology    : 363
% 6.50/2.31  #SimpNegUnit  : 51
% 6.50/2.31  #BackRed      : 10
% 6.50/2.31  
% 6.50/2.31  #Partial instantiations: 0
% 6.50/2.31  #Strategies tried      : 1
% 6.50/2.31  
% 6.50/2.31  Timing (in seconds)
% 6.50/2.31  ----------------------
% 6.50/2.32  Preprocessing        : 0.34
% 6.50/2.32  Parsing              : 0.17
% 6.50/2.32  CNF conversion       : 0.03
% 6.50/2.32  Main loop            : 1.16
% 6.50/2.32  Inferencing          : 0.37
% 6.50/2.32  Reduction            : 0.31
% 6.50/2.32  Demodulation         : 0.20
% 6.50/2.32  BG Simplification    : 0.07
% 6.50/2.32  Subsumption          : 0.31
% 6.50/2.32  Abstraction          : 0.06
% 6.50/2.32  MUC search           : 0.00
% 6.50/2.32  Cooper               : 0.00
% 6.50/2.32  Total                : 1.52
% 6.50/2.32  Index Insertion      : 0.00
% 6.50/2.32  Index Deletion       : 0.00
% 6.50/2.32  Index Matching       : 0.00
% 6.50/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
