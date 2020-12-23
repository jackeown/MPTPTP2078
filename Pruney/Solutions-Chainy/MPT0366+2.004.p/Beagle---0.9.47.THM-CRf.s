%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:44 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :   51 (  55 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 (  93 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_42,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_40,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    ! [B_26,A_27] :
      ( r1_xboole_0(B_26,A_27)
      | ~ r1_xboole_0(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_50])).

tff(c_72,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = A_32
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_79,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_53,c_72])).

tff(c_122,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_xboole_0(A_44,C_45)
      | ~ r1_tarski(A_44,k4_xboole_0(B_46,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [A_44] :
      ( r1_xboole_0(A_44,'#skF_6')
      | ~ r1_tarski(A_44,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_122])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_229,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,A_64)
      | ~ m1_subset_1(B_63,A_64)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_236,plain,(
    ! [B_63,A_11] :
      ( r1_tarski(B_63,A_11)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_229,c_14])).

tff(c_249,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_236])).

tff(c_269,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_249])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_275,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k3_subset_1(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_294,plain,(
    k4_xboole_0('#skF_3','#skF_6') = k3_subset_1('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_275])).

tff(c_355,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(A_81,k4_xboole_0(B_82,C_83))
      | ~ r1_xboole_0(A_81,C_83)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_455,plain,(
    ! [A_92] :
      ( r1_tarski(A_92,k3_subset_1('#skF_3','#skF_6'))
      | ~ r1_xboole_0(A_92,'#skF_6')
      | ~ r1_tarski(A_92,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_355])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_471,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_455,c_38])).

tff(c_478,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_471])).

tff(c_487,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_125,c_478])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:16:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  
% 2.75/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.75/1.38  
% 2.75/1.38  %Foreground sorts:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Background operators:
% 2.75/1.38  
% 2.75/1.38  
% 2.75/1.38  %Foreground operators:
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.75/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.75/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.75/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.75/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.75/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.38  
% 2.75/1.39  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 2.75/1.39  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.75/1.39  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.75/1.39  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.75/1.39  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.75/1.39  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.75/1.39  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.75/1.39  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.75/1.39  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.75/1.39  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.75/1.39  tff(c_40, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.75/1.39  tff(c_50, plain, (![B_26, A_27]: (r1_xboole_0(B_26, A_27) | ~r1_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.75/1.39  tff(c_53, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_50])).
% 2.75/1.39  tff(c_72, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=A_32 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.39  tff(c_79, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_53, c_72])).
% 2.75/1.39  tff(c_122, plain, (![A_44, C_45, B_46]: (r1_xboole_0(A_44, C_45) | ~r1_tarski(A_44, k4_xboole_0(B_46, C_45)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.75/1.39  tff(c_125, plain, (![A_44]: (r1_xboole_0(A_44, '#skF_6') | ~r1_tarski(A_44, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_79, c_122])).
% 2.75/1.39  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.75/1.39  tff(c_36, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.75/1.39  tff(c_229, plain, (![B_63, A_64]: (r2_hidden(B_63, A_64) | ~m1_subset_1(B_63, A_64) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.75/1.39  tff(c_14, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.75/1.39  tff(c_236, plain, (![B_63, A_11]: (r1_tarski(B_63, A_11) | ~m1_subset_1(B_63, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_229, c_14])).
% 2.75/1.39  tff(c_249, plain, (![B_66, A_67]: (r1_tarski(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)))), inference(negUnitSimplification, [status(thm)], [c_36, c_236])).
% 2.75/1.39  tff(c_269, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_249])).
% 2.75/1.39  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.75/1.39  tff(c_275, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k3_subset_1(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.75/1.39  tff(c_294, plain, (k4_xboole_0('#skF_3', '#skF_6')=k3_subset_1('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_275])).
% 2.75/1.39  tff(c_355, plain, (![A_81, B_82, C_83]: (r1_tarski(A_81, k4_xboole_0(B_82, C_83)) | ~r1_xboole_0(A_81, C_83) | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.75/1.39  tff(c_455, plain, (![A_92]: (r1_tarski(A_92, k3_subset_1('#skF_3', '#skF_6')) | ~r1_xboole_0(A_92, '#skF_6') | ~r1_tarski(A_92, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_294, c_355])).
% 2.75/1.39  tff(c_38, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.75/1.39  tff(c_471, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_455, c_38])).
% 2.75/1.39  tff(c_478, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_269, c_471])).
% 2.75/1.39  tff(c_487, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_125, c_478])).
% 2.75/1.39  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_487])).
% 2.75/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/1.39  
% 2.75/1.39  Inference rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Ref     : 0
% 2.75/1.39  #Sup     : 115
% 2.75/1.39  #Fact    : 0
% 2.75/1.39  #Define  : 0
% 2.75/1.39  #Split   : 4
% 2.75/1.39  #Chain   : 0
% 2.75/1.39  #Close   : 0
% 2.75/1.39  
% 2.75/1.39  Ordering : KBO
% 2.75/1.39  
% 2.75/1.39  Simplification rules
% 2.75/1.39  ----------------------
% 2.75/1.39  #Subsume      : 11
% 2.75/1.39  #Demod        : 10
% 2.75/1.39  #Tautology    : 43
% 2.75/1.39  #SimpNegUnit  : 2
% 2.75/1.39  #BackRed      : 0
% 2.75/1.39  
% 2.75/1.39  #Partial instantiations: 0
% 2.75/1.39  #Strategies tried      : 1
% 2.75/1.39  
% 2.75/1.39  Timing (in seconds)
% 2.75/1.39  ----------------------
% 2.75/1.40  Preprocessing        : 0.32
% 2.75/1.40  Parsing              : 0.16
% 2.75/1.40  CNF conversion       : 0.02
% 2.75/1.40  Main loop            : 0.31
% 2.75/1.40  Inferencing          : 0.12
% 2.75/1.40  Reduction            : 0.08
% 2.75/1.40  Demodulation         : 0.05
% 2.75/1.40  BG Simplification    : 0.02
% 2.75/1.40  Subsumption          : 0.07
% 2.75/1.40  Abstraction          : 0.01
% 2.75/1.40  MUC search           : 0.00
% 2.75/1.40  Cooper               : 0.00
% 2.75/1.40  Total                : 0.65
% 2.75/1.40  Index Insertion      : 0.00
% 2.75/1.40  Index Deletion       : 0.00
% 2.75/1.40  Index Matching       : 0.00
% 2.75/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
