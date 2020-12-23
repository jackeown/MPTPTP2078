%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:45 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 143 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 395 expanded)
%              Number of equality atoms :    3 (  21 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
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
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_25,plain,(
    ! [B_18,A_19] :
      ( r1_xboole_0(B_18,A_19)
      | ~ r1_xboole_0(A_19,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_25])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [A_29,B_30] :
      ( k3_subset_1(A_29,k3_subset_1(A_29,B_30)) = B_30
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_73])).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_138,plain,(
    ! [B_45,A_46,C_47] :
      ( r1_xboole_0(B_45,k3_subset_1(A_46,C_47))
      | ~ r1_tarski(B_45,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_296,plain,(
    ! [A_58,A_59,C_60,B_61] :
      ( r1_xboole_0(A_58,k3_subset_1(A_59,C_60))
      | ~ r1_tarski(A_58,B_61)
      | ~ r1_tarski(B_61,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_59)) ) ),
    inference(resolution,[status(thm)],[c_138,c_4])).

tff(c_301,plain,(
    ! [A_62,C_63] :
      ( r1_xboole_0('#skF_2',k3_subset_1(A_62,C_63))
      | ~ r1_tarski('#skF_3',C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_62))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_62)) ) ),
    inference(resolution,[status(thm)],[c_18,c_296])).

tff(c_320,plain,
    ( r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_4'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_4'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_301])).

tff(c_329,plain,
    ( r1_xboole_0('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_4'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_320])).

tff(c_421,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_424,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_421])).

tff(c_428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_424])).

tff(c_430,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_4'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_215,plain,(
    ! [B_50,C_51,A_52] :
      ( r1_tarski(B_50,C_51)
      | ~ r1_xboole_0(B_50,k3_subset_1(A_52,C_51))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_52))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_238,plain,(
    ! [B_50] :
      ( r1_tarski(B_50,k3_subset_1('#skF_1','#skF_4'))
      | ~ r1_xboole_0(B_50,'#skF_4')
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_4'),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(B_50,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_215])).

tff(c_566,plain,(
    ! [B_73] :
      ( r1_tarski(B_73,k3_subset_1('#skF_1','#skF_4'))
      | ~ r1_xboole_0(B_73,'#skF_4')
      | ~ m1_subset_1(B_73,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_238])).

tff(c_429,plain,
    ( ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_4'))
    | r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_442,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_569,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_566,c_442])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_28,c_569])).

tff(c_587,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_702,plain,(
    ! [B_79] :
      ( r1_tarski(B_79,k3_subset_1('#skF_1','#skF_4'))
      | ~ r1_xboole_0(B_79,'#skF_4')
      | ~ m1_subset_1(B_79,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_238])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_715,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_702,c_14])).

tff(c_724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_587,c_715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.41  
% 2.88/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.41  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.88/1.41  
% 2.88/1.41  %Foreground sorts:
% 2.88/1.41  
% 2.88/1.41  
% 2.88/1.41  %Background operators:
% 2.88/1.41  
% 2.88/1.41  
% 2.88/1.41  %Foreground operators:
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.88/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.88/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.41  
% 2.88/1.42  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 2.88/1.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.88/1.42  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.88/1.42  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.88/1.42  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 2.88/1.42  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.88/1.42  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.88/1.42  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.88/1.42  tff(c_16, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.88/1.42  tff(c_25, plain, (![B_18, A_19]: (r1_xboole_0(B_18, A_19) | ~r1_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.88/1.42  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_25])).
% 2.88/1.42  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.88/1.42  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.88/1.42  tff(c_73, plain, (![A_29, B_30]: (k3_subset_1(A_29, k3_subset_1(A_29, B_30))=B_30 | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.88/1.42  tff(c_80, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_20, c_73])).
% 2.88/1.42  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.88/1.42  tff(c_138, plain, (![B_45, A_46, C_47]: (r1_xboole_0(B_45, k3_subset_1(A_46, C_47)) | ~r1_tarski(B_45, C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(A_46)) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.88/1.42  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.42  tff(c_296, plain, (![A_58, A_59, C_60, B_61]: (r1_xboole_0(A_58, k3_subset_1(A_59, C_60)) | ~r1_tarski(A_58, B_61) | ~r1_tarski(B_61, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(A_59)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_59)))), inference(resolution, [status(thm)], [c_138, c_4])).
% 2.88/1.42  tff(c_301, plain, (![A_62, C_63]: (r1_xboole_0('#skF_2', k3_subset_1(A_62, C_63)) | ~r1_tarski('#skF_3', C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_62)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_62)))), inference(resolution, [status(thm)], [c_18, c_296])).
% 2.88/1.42  tff(c_320, plain, (r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_4')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_80, c_301])).
% 2.88/1.42  tff(c_329, plain, (r1_xboole_0('#skF_2', '#skF_4') | ~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_4')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_4'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_320])).
% 2.88/1.42  tff(c_421, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_4'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_329])).
% 2.88/1.42  tff(c_424, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_421])).
% 2.88/1.42  tff(c_428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_424])).
% 2.88/1.42  tff(c_430, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_4'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_329])).
% 2.88/1.42  tff(c_215, plain, (![B_50, C_51, A_52]: (r1_tarski(B_50, C_51) | ~r1_xboole_0(B_50, k3_subset_1(A_52, C_51)) | ~m1_subset_1(C_51, k1_zfmisc_1(A_52)) | ~m1_subset_1(B_50, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.88/1.42  tff(c_238, plain, (![B_50]: (r1_tarski(B_50, k3_subset_1('#skF_1', '#skF_4')) | ~r1_xboole_0(B_50, '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_4'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(B_50, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_80, c_215])).
% 2.88/1.42  tff(c_566, plain, (![B_73]: (r1_tarski(B_73, k3_subset_1('#skF_1', '#skF_4')) | ~r1_xboole_0(B_73, '#skF_4') | ~m1_subset_1(B_73, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_430, c_238])).
% 2.88/1.42  tff(c_429, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_4')) | r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_329])).
% 2.88/1.42  tff(c_442, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_429])).
% 2.88/1.42  tff(c_569, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_566, c_442])).
% 2.88/1.42  tff(c_586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_28, c_569])).
% 2.88/1.42  tff(c_587, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_429])).
% 2.88/1.42  tff(c_702, plain, (![B_79]: (r1_tarski(B_79, k3_subset_1('#skF_1', '#skF_4')) | ~r1_xboole_0(B_79, '#skF_4') | ~m1_subset_1(B_79, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_430, c_238])).
% 2.88/1.42  tff(c_14, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.88/1.42  tff(c_715, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_702, c_14])).
% 2.88/1.42  tff(c_724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_587, c_715])).
% 2.88/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.42  
% 2.88/1.42  Inference rules
% 2.88/1.42  ----------------------
% 2.88/1.42  #Ref     : 0
% 2.88/1.42  #Sup     : 172
% 2.88/1.42  #Fact    : 0
% 2.88/1.42  #Define  : 0
% 2.88/1.42  #Split   : 13
% 2.88/1.42  #Chain   : 0
% 2.88/1.42  #Close   : 0
% 2.88/1.42  
% 2.88/1.42  Ordering : KBO
% 2.88/1.42  
% 2.88/1.42  Simplification rules
% 2.88/1.42  ----------------------
% 2.88/1.42  #Subsume      : 34
% 2.88/1.42  #Demod        : 60
% 2.88/1.42  #Tautology    : 34
% 2.88/1.42  #SimpNegUnit  : 0
% 2.88/1.42  #BackRed      : 0
% 2.88/1.42  
% 2.88/1.42  #Partial instantiations: 0
% 2.88/1.42  #Strategies tried      : 1
% 2.88/1.42  
% 2.88/1.42  Timing (in seconds)
% 2.88/1.42  ----------------------
% 2.88/1.43  Preprocessing        : 0.28
% 2.88/1.43  Parsing              : 0.16
% 2.88/1.43  CNF conversion       : 0.02
% 2.88/1.43  Main loop            : 0.40
% 2.88/1.43  Inferencing          : 0.15
% 2.88/1.43  Reduction            : 0.11
% 2.88/1.43  Demodulation         : 0.07
% 2.88/1.43  BG Simplification    : 0.02
% 2.88/1.43  Subsumption          : 0.10
% 2.88/1.43  Abstraction          : 0.02
% 2.88/1.43  MUC search           : 0.00
% 2.88/1.43  Cooper               : 0.00
% 2.88/1.43  Total                : 0.71
% 2.88/1.43  Index Insertion      : 0.00
% 2.88/1.43  Index Deletion       : 0.00
% 2.88/1.43  Index Matching       : 0.00
% 2.88/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
