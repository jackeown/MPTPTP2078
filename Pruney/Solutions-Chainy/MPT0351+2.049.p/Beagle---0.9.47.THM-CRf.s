%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:43 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   43 (  69 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 ( 127 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_23,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_70,plain,(
    ! [A_30,B_31,C_32] :
      ( k4_subset_1(A_30,B_31,C_32) = k2_xboole_0(B_31,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_94,plain,(
    ! [A_34,B_35] :
      ( k4_subset_1(A_34,B_35,A_34) = k2_xboole_0(B_35,A_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(resolution,[status(thm)],[c_23,c_70])).

tff(c_99,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_94])).

tff(c_20,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_20])).

tff(c_101,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_24])).

tff(c_130,plain,(
    ! [A_43,B_44,C_45] :
      ( r2_hidden('#skF_1'(A_43,B_44,C_45),B_44)
      | r1_tarski(B_44,C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_190,plain,(
    ! [A_51,B_52,C_53,A_54] :
      ( r2_hidden('#skF_1'(A_51,B_52,C_53),A_54)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_54))
      | r1_tarski(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(resolution,[status(thm)],[c_130,c_10])).

tff(c_14,plain,(
    ! [A_14,B_15,C_19] :
      ( ~ r2_hidden('#skF_1'(A_14,B_15,C_19),C_19)
      | r1_tarski(B_15,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_199,plain,(
    ! [B_55,A_56,A_57] :
      ( ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | r1_tarski(B_55,A_56)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_190,c_14])).

tff(c_208,plain,(
    ! [A_57] :
      ( r1_tarski('#skF_3','#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_57))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_22,c_199])).

tff(c_212,plain,(
    ! [A_58] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_58))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_58)) ) ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_216,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_23,c_212])).

tff(c_220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_216])).

tff(c_221,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_224,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_221,c_4])).

tff(c_228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  
% 2.17/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.17/1.31  
% 2.17/1.31  %Foreground sorts:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Background operators:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Foreground operators:
% 2.17/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.17/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.31  
% 2.17/1.32  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.17/1.32  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.17/1.32  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.17/1.32  tff(f_48, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.17/1.32  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.17/1.32  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.17/1.32  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.17/1.32  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.17/1.32  tff(c_6, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.32  tff(c_8, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.32  tff(c_23, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.17/1.32  tff(c_70, plain, (![A_30, B_31, C_32]: (k4_subset_1(A_30, B_31, C_32)=k2_xboole_0(B_31, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.17/1.32  tff(c_94, plain, (![A_34, B_35]: (k4_subset_1(A_34, B_35, A_34)=k2_xboole_0(B_35, A_34) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(resolution, [status(thm)], [c_23, c_70])).
% 2.17/1.32  tff(c_99, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_94])).
% 2.17/1.32  tff(c_20, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.17/1.32  tff(c_24, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_20])).
% 2.17/1.32  tff(c_101, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_24])).
% 2.17/1.32  tff(c_130, plain, (![A_43, B_44, C_45]: (r2_hidden('#skF_1'(A_43, B_44, C_45), B_44) | r1_tarski(B_44, C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.32  tff(c_10, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.32  tff(c_190, plain, (![A_51, B_52, C_53, A_54]: (r2_hidden('#skF_1'(A_51, B_52, C_53), A_54) | ~m1_subset_1(B_52, k1_zfmisc_1(A_54)) | r1_tarski(B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(resolution, [status(thm)], [c_130, c_10])).
% 2.17/1.32  tff(c_14, plain, (![A_14, B_15, C_19]: (~r2_hidden('#skF_1'(A_14, B_15, C_19), C_19) | r1_tarski(B_15, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.32  tff(c_199, plain, (![B_55, A_56, A_57]: (~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | r1_tarski(B_55, A_56) | ~m1_subset_1(A_56, k1_zfmisc_1(A_57)) | ~m1_subset_1(B_55, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_190, c_14])).
% 2.17/1.32  tff(c_208, plain, (![A_57]: (r1_tarski('#skF_3', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(A_57)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_22, c_199])).
% 2.17/1.32  tff(c_212, plain, (![A_58]: (~m1_subset_1('#skF_2', k1_zfmisc_1(A_58)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_58)))), inference(splitLeft, [status(thm)], [c_208])).
% 2.17/1.32  tff(c_216, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_23, c_212])).
% 2.17/1.32  tff(c_220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_216])).
% 2.17/1.32  tff(c_221, plain, (r1_tarski('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_208])).
% 2.17/1.32  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.32  tff(c_224, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_221, c_4])).
% 2.17/1.32  tff(c_228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_224])).
% 2.17/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.32  
% 2.17/1.32  Inference rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Ref     : 0
% 2.17/1.32  #Sup     : 49
% 2.17/1.32  #Fact    : 0
% 2.17/1.32  #Define  : 0
% 2.17/1.32  #Split   : 1
% 2.17/1.32  #Chain   : 0
% 2.17/1.32  #Close   : 0
% 2.17/1.32  
% 2.17/1.32  Ordering : KBO
% 2.17/1.32  
% 2.17/1.32  Simplification rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Subsume      : 4
% 2.17/1.32  #Demod        : 14
% 2.17/1.32  #Tautology    : 26
% 2.17/1.32  #SimpNegUnit  : 1
% 2.17/1.32  #BackRed      : 3
% 2.17/1.33  
% 2.17/1.33  #Partial instantiations: 0
% 2.17/1.33  #Strategies tried      : 1
% 2.17/1.33  
% 2.17/1.33  Timing (in seconds)
% 2.17/1.33  ----------------------
% 2.17/1.33  Preprocessing        : 0.31
% 2.17/1.33  Parsing              : 0.16
% 2.17/1.33  CNF conversion       : 0.02
% 2.17/1.33  Main loop            : 0.20
% 2.17/1.33  Inferencing          : 0.07
% 2.17/1.33  Reduction            : 0.06
% 2.17/1.33  Demodulation         : 0.05
% 2.17/1.33  BG Simplification    : 0.01
% 2.17/1.33  Subsumption          : 0.04
% 2.17/1.33  Abstraction          : 0.01
% 2.17/1.33  MUC search           : 0.00
% 2.17/1.33  Cooper               : 0.00
% 2.17/1.33  Total                : 0.54
% 2.17/1.33  Index Insertion      : 0.00
% 2.17/1.33  Index Deletion       : 0.00
% 2.17/1.33  Index Matching       : 0.00
% 2.17/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
