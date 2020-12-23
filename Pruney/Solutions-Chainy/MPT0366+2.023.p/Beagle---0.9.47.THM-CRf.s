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
% DateTime   : Thu Dec  3 09:56:47 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   43 (  63 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 157 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_68,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [B_11,A_10,C_13] :
      ( r1_tarski(B_11,k3_subset_1(A_10,C_13))
      | ~ r1_xboole_0(B_11,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_67,plain,(
    ! [C_36,A_37,B_38] :
      ( r1_tarski(C_36,k3_subset_1(A_37,B_38))
      | ~ r1_tarski(B_38,k3_subset_1(A_37,C_36))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    ! [C_39,A_40,B_41] :
      ( r1_tarski(C_39,k3_subset_1(A_40,B_41))
      | ~ r1_xboole_0(B_41,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_40))
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(resolution,[status(thm)],[c_14,c_67])).

tff(c_12,plain,(
    ! [B_11,C_13,A_10] :
      ( r1_xboole_0(B_11,C_13)
      | ~ r1_tarski(B_11,k3_subset_1(A_10,C_13))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,(
    ! [C_42,B_43,A_44] :
      ( r1_xboole_0(C_42,B_43)
      | ~ r1_xboole_0(B_43,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_75,c_12])).

tff(c_102,plain,(
    ! [A_44] :
      ( r1_xboole_0('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_44))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_18,c_93])).

tff(c_104,plain,(
    ! [A_45] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_45))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_45)) ) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_107,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_104])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_107])).

tff(c_112,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = A_4
      | ~ r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_112,c_6])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_48] :
      ( r1_xboole_0(A_48,'#skF_4')
      | ~ r1_tarski(A_48,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_2])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_56,plain,(
    ! [B_33,A_34,C_35] :
      ( r1_tarski(B_33,k3_subset_1(A_34,C_35))
      | ~ r1_xboole_0(B_33,C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_56,c_16])).

tff(c_66,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_62])).

tff(c_140,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_66])).

tff(c_148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.34  
% 2.07/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.34  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.07/1.34  
% 2.07/1.34  %Foreground sorts:
% 2.07/1.34  
% 2.07/1.34  
% 2.07/1.34  %Background operators:
% 2.07/1.34  
% 2.07/1.34  
% 2.07/1.34  %Foreground operators:
% 2.07/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.07/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.34  
% 2.07/1.36  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 2.07/1.36  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.07/1.36  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.07/1.36  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.07/1.36  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.07/1.36  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.36  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.36  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.36  tff(c_18, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.36  tff(c_14, plain, (![B_11, A_10, C_13]: (r1_tarski(B_11, k3_subset_1(A_10, C_13)) | ~r1_xboole_0(B_11, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.36  tff(c_67, plain, (![C_36, A_37, B_38]: (r1_tarski(C_36, k3_subset_1(A_37, B_38)) | ~r1_tarski(B_38, k3_subset_1(A_37, C_36)) | ~m1_subset_1(C_36, k1_zfmisc_1(A_37)) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.36  tff(c_75, plain, (![C_39, A_40, B_41]: (r1_tarski(C_39, k3_subset_1(A_40, B_41)) | ~r1_xboole_0(B_41, C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(A_40)) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(resolution, [status(thm)], [c_14, c_67])).
% 2.07/1.36  tff(c_12, plain, (![B_11, C_13, A_10]: (r1_xboole_0(B_11, C_13) | ~r1_tarski(B_11, k3_subset_1(A_10, C_13)) | ~m1_subset_1(C_13, k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.36  tff(c_93, plain, (![C_42, B_43, A_44]: (r1_xboole_0(C_42, B_43) | ~r1_xboole_0(B_43, C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(A_44)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)))), inference(resolution, [status(thm)], [c_75, c_12])).
% 2.07/1.36  tff(c_102, plain, (![A_44]: (r1_xboole_0('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_44)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_44)))), inference(resolution, [status(thm)], [c_18, c_93])).
% 2.07/1.36  tff(c_104, plain, (![A_45]: (~m1_subset_1('#skF_3', k1_zfmisc_1(A_45)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_45)))), inference(splitLeft, [status(thm)], [c_102])).
% 2.07/1.36  tff(c_107, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_104])).
% 2.07/1.36  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_107])).
% 2.07/1.36  tff(c_112, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_102])).
% 2.07/1.36  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=A_4 | ~r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.36  tff(c_120, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_112, c_6])).
% 2.07/1.36  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.36  tff(c_135, plain, (![A_48]: (r1_xboole_0(A_48, '#skF_4') | ~r1_tarski(A_48, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_2])).
% 2.07/1.36  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.36  tff(c_56, plain, (![B_33, A_34, C_35]: (r1_tarski(B_33, k3_subset_1(A_34, C_35)) | ~r1_xboole_0(B_33, C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(A_34)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.36  tff(c_16, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.07/1.36  tff(c_62, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_56, c_16])).
% 2.07/1.36  tff(c_66, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_62])).
% 2.07/1.36  tff(c_140, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_135, c_66])).
% 2.07/1.36  tff(c_148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_140])).
% 2.07/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.36  
% 2.07/1.36  Inference rules
% 2.07/1.36  ----------------------
% 2.07/1.36  #Ref     : 0
% 2.07/1.36  #Sup     : 29
% 2.07/1.36  #Fact    : 0
% 2.07/1.36  #Define  : 0
% 2.07/1.36  #Split   : 1
% 2.07/1.36  #Chain   : 0
% 2.07/1.36  #Close   : 0
% 2.07/1.36  
% 2.07/1.36  Ordering : KBO
% 2.07/1.36  
% 2.07/1.36  Simplification rules
% 2.07/1.36  ----------------------
% 2.07/1.36  #Subsume      : 1
% 2.07/1.36  #Demod        : 7
% 2.07/1.36  #Tautology    : 9
% 2.07/1.36  #SimpNegUnit  : 0
% 2.07/1.36  #BackRed      : 0
% 2.07/1.36  
% 2.07/1.36  #Partial instantiations: 0
% 2.07/1.36  #Strategies tried      : 1
% 2.07/1.36  
% 2.07/1.36  Timing (in seconds)
% 2.07/1.36  ----------------------
% 2.07/1.36  Preprocessing        : 0.33
% 2.07/1.36  Parsing              : 0.20
% 2.07/1.36  CNF conversion       : 0.02
% 2.07/1.36  Main loop            : 0.19
% 2.07/1.36  Inferencing          : 0.08
% 2.07/1.36  Reduction            : 0.05
% 2.07/1.36  Demodulation         : 0.03
% 2.07/1.36  BG Simplification    : 0.02
% 2.07/1.36  Subsumption          : 0.04
% 2.07/1.36  Abstraction          : 0.01
% 2.07/1.36  MUC search           : 0.00
% 2.07/1.36  Cooper               : 0.00
% 2.07/1.36  Total                : 0.56
% 2.07/1.36  Index Insertion      : 0.00
% 2.07/1.36  Index Deletion       : 0.00
% 2.07/1.36  Index Matching       : 0.00
% 2.07/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
