%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:44 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   48 (  52 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 (  89 expanded)
%              Number of equality atoms :    4 (   4 expanded)
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

tff(f_83,negated_conjecture,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_68,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_36,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_44])).

tff(c_113,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_xboole_0(A_40,C_41)
      | ~ r1_xboole_0(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    ! [A_40] :
      ( r1_xboole_0(A_40,'#skF_6')
      | ~ r1_tarski(A_40,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_47,c_113])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_76,plain,(
    ! [B_34,A_35] :
      ( r2_hidden(B_34,A_35)
      | ~ m1_subset_1(B_34,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,(
    ! [B_34,A_9] :
      ( r1_tarski(B_34,A_9)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_76,c_8])).

tff(c_84,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(B_36,A_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_80])).

tff(c_100,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_84])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_157,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k3_subset_1(A_49,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_176,plain,(
    k4_xboole_0('#skF_3','#skF_6') = k3_subset_1('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_157])).

tff(c_207,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_tarski(A_53,k4_xboole_0(B_54,C_55))
      | ~ r1_xboole_0(A_53,C_55)
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_294,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,k3_subset_1('#skF_3','#skF_6'))
      | ~ r1_xboole_0(A_66,'#skF_6')
      | ~ r1_tarski(A_66,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_207])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_304,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_294,c_32])).

tff(c_310,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_304])).

tff(c_319,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_118,c_310])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:06:52 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.14/1.26  
% 2.14/1.26  %Foreground sorts:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Background operators:
% 2.14/1.26  
% 2.14/1.26  
% 2.14/1.26  %Foreground operators:
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.26  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.14/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.14/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.14/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.26  
% 2.14/1.27  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 2.14/1.27  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.14/1.27  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.14/1.27  tff(f_68, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.14/1.27  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.14/1.27  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.14/1.27  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.14/1.27  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.14/1.27  tff(c_36, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.27  tff(c_34, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.27  tff(c_44, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.27  tff(c_47, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_34, c_44])).
% 2.14/1.27  tff(c_113, plain, (![A_40, C_41, B_42]: (r1_xboole_0(A_40, C_41) | ~r1_xboole_0(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.27  tff(c_118, plain, (![A_40]: (r1_xboole_0(A_40, '#skF_6') | ~r1_tarski(A_40, '#skF_5'))), inference(resolution, [status(thm)], [c_47, c_113])).
% 2.14/1.27  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.27  tff(c_30, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.14/1.27  tff(c_76, plain, (![B_34, A_35]: (r2_hidden(B_34, A_35) | ~m1_subset_1(B_34, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.27  tff(c_8, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.27  tff(c_80, plain, (![B_34, A_9]: (r1_tarski(B_34, A_9) | ~m1_subset_1(B_34, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_76, c_8])).
% 2.14/1.27  tff(c_84, plain, (![B_36, A_37]: (r1_tarski(B_36, A_37) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)))), inference(negUnitSimplification, [status(thm)], [c_30, c_80])).
% 2.14/1.27  tff(c_100, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_84])).
% 2.14/1.27  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.27  tff(c_157, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k3_subset_1(A_49, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.14/1.27  tff(c_176, plain, (k4_xboole_0('#skF_3', '#skF_6')=k3_subset_1('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_38, c_157])).
% 2.14/1.27  tff(c_207, plain, (![A_53, B_54, C_55]: (r1_tarski(A_53, k4_xboole_0(B_54, C_55)) | ~r1_xboole_0(A_53, C_55) | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.27  tff(c_294, plain, (![A_66]: (r1_tarski(A_66, k3_subset_1('#skF_3', '#skF_6')) | ~r1_xboole_0(A_66, '#skF_6') | ~r1_tarski(A_66, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_207])).
% 2.14/1.27  tff(c_32, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.27  tff(c_304, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_294, c_32])).
% 2.14/1.27  tff(c_310, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_304])).
% 2.14/1.27  tff(c_319, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_118, c_310])).
% 2.14/1.27  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_319])).
% 2.14/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.27  
% 2.14/1.27  Inference rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Ref     : 0
% 2.14/1.27  #Sup     : 71
% 2.14/1.27  #Fact    : 0
% 2.14/1.27  #Define  : 0
% 2.14/1.27  #Split   : 4
% 2.14/1.27  #Chain   : 0
% 2.14/1.27  #Close   : 0
% 2.14/1.27  
% 2.14/1.27  Ordering : KBO
% 2.14/1.27  
% 2.14/1.27  Simplification rules
% 2.14/1.27  ----------------------
% 2.14/1.27  #Subsume      : 12
% 2.14/1.27  #Demod        : 9
% 2.14/1.27  #Tautology    : 19
% 2.14/1.27  #SimpNegUnit  : 2
% 2.14/1.27  #BackRed      : 0
% 2.14/1.27  
% 2.14/1.27  #Partial instantiations: 0
% 2.14/1.27  #Strategies tried      : 1
% 2.14/1.27  
% 2.14/1.27  Timing (in seconds)
% 2.14/1.27  ----------------------
% 2.14/1.27  Preprocessing        : 0.30
% 2.14/1.27  Parsing              : 0.16
% 2.14/1.27  CNF conversion       : 0.02
% 2.14/1.27  Main loop            : 0.23
% 2.14/1.27  Inferencing          : 0.08
% 2.14/1.27  Reduction            : 0.06
% 2.14/1.27  Demodulation         : 0.04
% 2.14/1.27  BG Simplification    : 0.02
% 2.14/1.27  Subsumption          : 0.06
% 2.14/1.27  Abstraction          : 0.01
% 2.14/1.27  MUC search           : 0.00
% 2.14/1.27  Cooper               : 0.00
% 2.14/1.27  Total                : 0.55
% 2.14/1.27  Index Insertion      : 0.00
% 2.14/1.27  Index Deletion       : 0.00
% 2.14/1.27  Index Matching       : 0.00
% 2.14/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
