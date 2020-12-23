%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:54 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   50 (  62 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 ( 116 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_56,plain,(
    ! [B_22,A_23] :
      ( v1_xboole_0(B_22)
      | ~ m1_subset_1(B_22,A_23)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_64,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_56])).

tff(c_65,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_38,plain,(
    ! [B_14,A_13] :
      ( r2_hidden(B_14,A_13)
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_119,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k3_subset_1(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_128,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_119])).

tff(c_34,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_151,plain,(
    ! [A_46,C_47,B_48] :
      ( r2_hidden(A_46,C_47)
      | ~ r2_hidden(A_46,B_48)
      | r2_hidden(A_46,k5_xboole_0(B_48,C_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_248,plain,(
    ! [A_72,A_73,B_74] :
      ( r2_hidden(A_72,k3_xboole_0(A_73,B_74))
      | ~ r2_hidden(A_72,A_73)
      | r2_hidden(A_72,k4_xboole_0(A_73,B_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_151])).

tff(c_294,plain,(
    ! [A_78] :
      ( r2_hidden(A_78,k3_xboole_0('#skF_3','#skF_4'))
      | ~ r2_hidden(A_78,'#skF_3')
      | r2_hidden(A_78,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_248])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_316,plain,(
    ! [A_79] :
      ( r2_hidden(A_79,'#skF_4')
      | ~ r2_hidden(A_79,'#skF_3')
      | r2_hidden(A_79,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_294,c_4])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_329,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_316,c_46])).

tff(c_337,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_329])).

tff(c_340,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_337])).

tff(c_343,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_340])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_343])).

tff(c_347,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_20,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_359,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_347,c_20])).

tff(c_363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n022.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 16:26:55 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.24  
% 2.27/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.25  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.27/1.25  
% 2.27/1.25  %Foreground sorts:
% 2.27/1.25  
% 2.27/1.25  
% 2.27/1.25  %Background operators:
% 2.27/1.25  
% 2.27/1.25  
% 2.27/1.25  %Foreground operators:
% 2.27/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.27/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.27/1.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.27/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.27/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.25  
% 2.27/1.26  tff(f_79, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.27/1.26  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.27/1.26  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.27/1.26  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.27/1.26  tff(f_45, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.27/1.26  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.27/1.26  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.27/1.26  tff(c_54, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.27/1.26  tff(c_50, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.27/1.26  tff(c_56, plain, (![B_22, A_23]: (v1_xboole_0(B_22) | ~m1_subset_1(B_22, A_23) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.26  tff(c_64, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_56])).
% 2.27/1.26  tff(c_65, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 2.27/1.26  tff(c_38, plain, (![B_14, A_13]: (r2_hidden(B_14, A_13) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.26  tff(c_48, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.27/1.26  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.27/1.26  tff(c_119, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k3_subset_1(A_38, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.27/1.26  tff(c_128, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_119])).
% 2.27/1.26  tff(c_34, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.27/1.26  tff(c_151, plain, (![A_46, C_47, B_48]: (r2_hidden(A_46, C_47) | ~r2_hidden(A_46, B_48) | r2_hidden(A_46, k5_xboole_0(B_48, C_47)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.26  tff(c_248, plain, (![A_72, A_73, B_74]: (r2_hidden(A_72, k3_xboole_0(A_73, B_74)) | ~r2_hidden(A_72, A_73) | r2_hidden(A_72, k4_xboole_0(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_151])).
% 2.27/1.26  tff(c_294, plain, (![A_78]: (r2_hidden(A_78, k3_xboole_0('#skF_3', '#skF_4')) | ~r2_hidden(A_78, '#skF_3') | r2_hidden(A_78, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_128, c_248])).
% 2.27/1.26  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.27/1.26  tff(c_316, plain, (![A_79]: (r2_hidden(A_79, '#skF_4') | ~r2_hidden(A_79, '#skF_3') | r2_hidden(A_79, k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_294, c_4])).
% 2.27/1.26  tff(c_46, plain, (~r2_hidden('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.27/1.26  tff(c_329, plain, (r2_hidden('#skF_5', '#skF_4') | ~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_316, c_46])).
% 2.27/1.26  tff(c_337, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_329])).
% 2.27/1.26  tff(c_340, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_337])).
% 2.27/1.26  tff(c_343, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_340])).
% 2.27/1.26  tff(c_345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_343])).
% 2.27/1.26  tff(c_347, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_64])).
% 2.27/1.26  tff(c_20, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.27/1.26  tff(c_359, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_347, c_20])).
% 2.27/1.26  tff(c_363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_359])).
% 2.27/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.26  
% 2.27/1.26  Inference rules
% 2.27/1.26  ----------------------
% 2.27/1.26  #Ref     : 0
% 2.27/1.26  #Sup     : 63
% 2.27/1.26  #Fact    : 0
% 2.27/1.26  #Define  : 0
% 2.27/1.26  #Split   : 6
% 2.27/1.26  #Chain   : 0
% 2.27/1.26  #Close   : 0
% 2.27/1.26  
% 2.27/1.26  Ordering : KBO
% 2.27/1.26  
% 2.27/1.26  Simplification rules
% 2.27/1.26  ----------------------
% 2.27/1.26  #Subsume      : 2
% 2.27/1.26  #Demod        : 1
% 2.27/1.26  #Tautology    : 22
% 2.27/1.26  #SimpNegUnit  : 5
% 2.27/1.26  #BackRed      : 0
% 2.27/1.26  
% 2.27/1.26  #Partial instantiations: 0
% 2.27/1.26  #Strategies tried      : 1
% 2.27/1.26  
% 2.27/1.26  Timing (in seconds)
% 2.27/1.26  ----------------------
% 2.27/1.26  Preprocessing        : 0.30
% 2.27/1.26  Parsing              : 0.15
% 2.27/1.26  CNF conversion       : 0.02
% 2.27/1.26  Main loop            : 0.24
% 2.27/1.26  Inferencing          : 0.09
% 2.27/1.26  Reduction            : 0.06
% 2.27/1.26  Demodulation         : 0.03
% 2.27/1.26  BG Simplification    : 0.02
% 2.27/1.26  Subsumption          : 0.06
% 2.27/1.26  Abstraction          : 0.01
% 2.27/1.26  MUC search           : 0.00
% 2.27/1.26  Cooper               : 0.00
% 2.27/1.26  Total                : 0.57
% 2.27/1.26  Index Insertion      : 0.00
% 2.27/1.26  Index Deletion       : 0.00
% 2.27/1.26  Index Matching       : 0.00
% 2.27/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
