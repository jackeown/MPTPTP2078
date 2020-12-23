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
% DateTime   : Thu Dec  3 09:56:44 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   51 (  55 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   71 (  95 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_123,plain,(
    ! [B_49,A_50] :
      ( r2_hidden(B_49,A_50)
      | ~ m1_subset_1(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_130,plain,(
    ! [B_49,A_11] :
      ( r1_tarski(B_49,A_11)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_11))
      | v1_xboole_0(k1_zfmisc_1(A_11)) ) ),
    inference(resolution,[status(thm)],[c_123,c_14])).

tff(c_135,plain,(
    ! [B_51,A_52] :
      ( r1_tarski(B_51,A_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_130])).

tff(c_155,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_135])).

tff(c_40,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_58,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_58])).

tff(c_103,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_xboole_0(A_42,B_43)
      | ~ r1_xboole_0(A_42,k2_xboole_0(B_43,C_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_107,plain,(
    ! [A_45] :
      ( r1_xboole_0(A_45,'#skF_4')
      | ~ r1_xboole_0(A_45,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_103])).

tff(c_111,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_114,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_111,c_2])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_161,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k3_subset_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_180,plain,(
    k4_xboole_0('#skF_3','#skF_6') = k3_subset_1('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_161])).

tff(c_237,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k4_xboole_0(B_57,C_58))
      | ~ r1_xboole_0(A_56,C_58)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_389,plain,(
    ! [A_75] :
      ( r1_tarski(A_75,k3_subset_1('#skF_3','#skF_6'))
      | ~ r1_xboole_0(A_75,'#skF_6')
      | ~ r1_tarski(A_75,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_237])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_398,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_389,c_38])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_114,c_398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.31  
% 2.23/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.23/1.31  
% 2.23/1.31  %Foreground sorts:
% 2.23/1.31  
% 2.23/1.31  
% 2.23/1.31  %Background operators:
% 2.23/1.31  
% 2.23/1.31  
% 2.23/1.31  %Foreground operators:
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.23/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.31  
% 2.55/1.32  tff(f_97, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 2.55/1.32  tff(f_82, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.55/1.32  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.55/1.32  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.55/1.32  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.55/1.32  tff(f_49, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.55/1.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.55/1.32  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.55/1.32  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.55/1.32  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.55/1.32  tff(c_36, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.32  tff(c_123, plain, (![B_49, A_50]: (r2_hidden(B_49, A_50) | ~m1_subset_1(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.55/1.32  tff(c_14, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.55/1.32  tff(c_130, plain, (![B_49, A_11]: (r1_tarski(B_49, A_11) | ~m1_subset_1(B_49, k1_zfmisc_1(A_11)) | v1_xboole_0(k1_zfmisc_1(A_11)))), inference(resolution, [status(thm)], [c_123, c_14])).
% 2.55/1.32  tff(c_135, plain, (![B_51, A_52]: (r1_tarski(B_51, A_52) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)))), inference(negUnitSimplification, [status(thm)], [c_36, c_130])).
% 2.55/1.32  tff(c_155, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_135])).
% 2.55/1.32  tff(c_40, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.55/1.32  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.55/1.32  tff(c_58, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.55/1.32  tff(c_62, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_42, c_58])).
% 2.55/1.32  tff(c_103, plain, (![A_42, B_43, C_44]: (r1_xboole_0(A_42, B_43) | ~r1_xboole_0(A_42, k2_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.32  tff(c_107, plain, (![A_45]: (r1_xboole_0(A_45, '#skF_4') | ~r1_xboole_0(A_45, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_103])).
% 2.55/1.32  tff(c_111, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_107])).
% 2.55/1.32  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.32  tff(c_114, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_111, c_2])).
% 2.55/1.32  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.55/1.32  tff(c_161, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k3_subset_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.55/1.32  tff(c_180, plain, (k4_xboole_0('#skF_3', '#skF_6')=k3_subset_1('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_161])).
% 2.55/1.32  tff(c_237, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k4_xboole_0(B_57, C_58)) | ~r1_xboole_0(A_56, C_58) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.55/1.32  tff(c_389, plain, (![A_75]: (r1_tarski(A_75, k3_subset_1('#skF_3', '#skF_6')) | ~r1_xboole_0(A_75, '#skF_6') | ~r1_tarski(A_75, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_180, c_237])).
% 2.55/1.32  tff(c_38, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.55/1.32  tff(c_398, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_389, c_38])).
% 2.55/1.32  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_114, c_398])).
% 2.55/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.32  
% 2.55/1.32  Inference rules
% 2.55/1.32  ----------------------
% 2.55/1.32  #Ref     : 0
% 2.55/1.32  #Sup     : 92
% 2.55/1.32  #Fact    : 0
% 2.55/1.32  #Define  : 0
% 2.55/1.32  #Split   : 0
% 2.55/1.32  #Chain   : 0
% 2.55/1.32  #Close   : 0
% 2.55/1.32  
% 2.55/1.32  Ordering : KBO
% 2.55/1.32  
% 2.55/1.32  Simplification rules
% 2.55/1.32  ----------------------
% 2.55/1.32  #Subsume      : 12
% 2.55/1.32  #Demod        : 7
% 2.55/1.32  #Tautology    : 35
% 2.55/1.32  #SimpNegUnit  : 2
% 2.55/1.32  #BackRed      : 0
% 2.55/1.32  
% 2.55/1.32  #Partial instantiations: 0
% 2.55/1.32  #Strategies tried      : 1
% 2.55/1.32  
% 2.55/1.32  Timing (in seconds)
% 2.55/1.32  ----------------------
% 2.55/1.32  Preprocessing        : 0.31
% 2.55/1.32  Parsing              : 0.16
% 2.55/1.32  CNF conversion       : 0.02
% 2.55/1.32  Main loop            : 0.25
% 2.55/1.32  Inferencing          : 0.10
% 2.55/1.32  Reduction            : 0.07
% 2.55/1.32  Demodulation         : 0.05
% 2.55/1.32  BG Simplification    : 0.02
% 2.55/1.32  Subsumption          : 0.05
% 2.55/1.32  Abstraction          : 0.01
% 2.55/1.32  MUC search           : 0.00
% 2.55/1.32  Cooper               : 0.00
% 2.55/1.33  Total                : 0.59
% 2.55/1.33  Index Insertion      : 0.00
% 2.55/1.33  Index Deletion       : 0.00
% 2.55/1.33  Index Matching       : 0.00
% 2.55/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
