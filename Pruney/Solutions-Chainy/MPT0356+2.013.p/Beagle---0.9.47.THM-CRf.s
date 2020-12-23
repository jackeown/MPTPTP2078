%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:57 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   53 (  62 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 107 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_84,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_77,axiom,(
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
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ! [A_23] : ~ v1_xboole_0(k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_85,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(B_44,A_45)
      | ~ m1_subset_1(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [C_18,A_14] :
      ( r1_tarski(C_18,A_14)
      | ~ r2_hidden(C_18,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_89,plain,(
    ! [B_44,A_14] :
      ( r1_tarski(B_44,A_14)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_14))
      | v1_xboole_0(k1_zfmisc_1(A_14)) ) ),
    inference(resolution,[status(thm)],[c_85,c_16])).

tff(c_93,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(B_46,A_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_89])).

tff(c_105,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_93])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_142,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k3_subset_1(A_57,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_158,plain,(
    k4_xboole_0('#skF_4','#skF_6') = k3_subset_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_142])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,C_10)
      | ~ r1_tarski(A_8,k4_xboole_0(B_9,C_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_180,plain,(
    ! [A_59] :
      ( r1_xboole_0(A_59,'#skF_6')
      | ~ r1_tarski(A_59,k3_subset_1('#skF_4','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_10])).

tff(c_184,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_180])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_203,plain,(
    ! [C_63] :
      ( ~ r2_hidden(C_63,'#skF_6')
      | ~ r2_hidden(C_63,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_184,c_2])).

tff(c_244,plain,(
    ! [A_68] :
      ( ~ r2_hidden('#skF_1'(A_68,'#skF_5'),'#skF_6')
      | r1_xboole_0(A_68,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4,c_203])).

tff(c_253,plain,(
    r1_xboole_0('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_244])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_159,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_142])).

tff(c_185,plain,(
    ! [A_60,B_61,C_62] :
      ( r1_tarski(A_60,k4_xboole_0(B_61,C_62))
      | ~ r1_xboole_0(A_60,C_62)
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_295,plain,(
    ! [A_73] :
      ( r1_tarski(A_73,k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_xboole_0(A_73,'#skF_5')
      | ~ r1_tarski(A_73,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_185])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_6',k3_subset_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_304,plain,
    ( ~ r1_xboole_0('#skF_6','#skF_5')
    | ~ r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_295,c_40])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_253,c_304])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.33  
% 2.16/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.16/1.33  
% 2.16/1.33  %Foreground sorts:
% 2.16/1.33  
% 2.16/1.33  
% 2.16/1.33  %Background operators:
% 2.16/1.33  
% 2.16/1.33  
% 2.16/1.33  %Foreground operators:
% 2.16/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.16/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.33  
% 2.16/1.34  tff(f_94, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 2.16/1.34  tff(f_84, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.16/1.34  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.16/1.34  tff(f_64, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.16/1.34  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.16/1.34  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.16/1.34  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.16/1.34  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.16/1.34  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.16/1.34  tff(c_38, plain, (![A_23]: (~v1_xboole_0(k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.16/1.34  tff(c_85, plain, (![B_44, A_45]: (r2_hidden(B_44, A_45) | ~m1_subset_1(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.16/1.34  tff(c_16, plain, (![C_18, A_14]: (r1_tarski(C_18, A_14) | ~r2_hidden(C_18, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.34  tff(c_89, plain, (![B_44, A_14]: (r1_tarski(B_44, A_14) | ~m1_subset_1(B_44, k1_zfmisc_1(A_14)) | v1_xboole_0(k1_zfmisc_1(A_14)))), inference(resolution, [status(thm)], [c_85, c_16])).
% 2.16/1.34  tff(c_93, plain, (![B_46, A_47]: (r1_tarski(B_46, A_47) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)))), inference(negUnitSimplification, [status(thm)], [c_38, c_89])).
% 2.16/1.34  tff(c_105, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_93])).
% 2.16/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.34  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.34  tff(c_42, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.16/1.34  tff(c_142, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k3_subset_1(A_57, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.16/1.34  tff(c_158, plain, (k4_xboole_0('#skF_4', '#skF_6')=k3_subset_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_44, c_142])).
% 2.16/1.34  tff(c_10, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, C_10) | ~r1_tarski(A_8, k4_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.34  tff(c_180, plain, (![A_59]: (r1_xboole_0(A_59, '#skF_6') | ~r1_tarski(A_59, k3_subset_1('#skF_4', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_158, c_10])).
% 2.16/1.34  tff(c_184, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_180])).
% 2.16/1.34  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.34  tff(c_203, plain, (![C_63]: (~r2_hidden(C_63, '#skF_6') | ~r2_hidden(C_63, '#skF_5'))), inference(resolution, [status(thm)], [c_184, c_2])).
% 2.16/1.34  tff(c_244, plain, (![A_68]: (~r2_hidden('#skF_1'(A_68, '#skF_5'), '#skF_6') | r1_xboole_0(A_68, '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_203])).
% 2.16/1.34  tff(c_253, plain, (r1_xboole_0('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_244])).
% 2.16/1.34  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.16/1.34  tff(c_159, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_142])).
% 2.16/1.34  tff(c_185, plain, (![A_60, B_61, C_62]: (r1_tarski(A_60, k4_xboole_0(B_61, C_62)) | ~r1_xboole_0(A_60, C_62) | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.16/1.34  tff(c_295, plain, (![A_73]: (r1_tarski(A_73, k3_subset_1('#skF_4', '#skF_5')) | ~r1_xboole_0(A_73, '#skF_5') | ~r1_tarski(A_73, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_185])).
% 2.16/1.34  tff(c_40, plain, (~r1_tarski('#skF_6', k3_subset_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.16/1.34  tff(c_304, plain, (~r1_xboole_0('#skF_6', '#skF_5') | ~r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_295, c_40])).
% 2.16/1.34  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_105, c_253, c_304])).
% 2.16/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.34  
% 2.16/1.34  Inference rules
% 2.16/1.34  ----------------------
% 2.16/1.34  #Ref     : 0
% 2.16/1.34  #Sup     : 56
% 2.16/1.34  #Fact    : 0
% 2.16/1.35  #Define  : 0
% 2.16/1.35  #Split   : 2
% 2.16/1.35  #Chain   : 0
% 2.16/1.35  #Close   : 0
% 2.16/1.35  
% 2.16/1.35  Ordering : KBO
% 2.16/1.35  
% 2.16/1.35  Simplification rules
% 2.16/1.35  ----------------------
% 2.16/1.35  #Subsume      : 6
% 2.16/1.35  #Demod        : 4
% 2.16/1.35  #Tautology    : 16
% 2.16/1.35  #SimpNegUnit  : 2
% 2.16/1.35  #BackRed      : 0
% 2.16/1.35  
% 2.16/1.35  #Partial instantiations: 0
% 2.16/1.35  #Strategies tried      : 1
% 2.16/1.35  
% 2.16/1.35  Timing (in seconds)
% 2.16/1.35  ----------------------
% 2.43/1.35  Preprocessing        : 0.33
% 2.43/1.35  Parsing              : 0.17
% 2.43/1.35  CNF conversion       : 0.02
% 2.43/1.35  Main loop            : 0.21
% 2.43/1.35  Inferencing          : 0.08
% 2.43/1.35  Reduction            : 0.05
% 2.43/1.35  Demodulation         : 0.03
% 2.43/1.35  BG Simplification    : 0.01
% 2.43/1.35  Subsumption          : 0.04
% 2.43/1.35  Abstraction          : 0.01
% 2.43/1.35  MUC search           : 0.00
% 2.43/1.35  Cooper               : 0.00
% 2.43/1.35  Total                : 0.56
% 2.43/1.35  Index Insertion      : 0.00
% 2.43/1.35  Index Deletion       : 0.00
% 2.43/1.35  Index Matching       : 0.00
% 2.43/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
