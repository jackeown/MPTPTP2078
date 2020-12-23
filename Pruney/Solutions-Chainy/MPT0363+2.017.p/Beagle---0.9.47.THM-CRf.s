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
% DateTime   : Thu Dec  3 09:56:38 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   56 (  72 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 ( 118 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_67,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_47,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_185,plain,(
    ! [B_57,A_58] :
      ( r2_hidden(B_57,A_58)
      | ~ m1_subset_1(B_57,A_58)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [A_13] : k3_tarski(k1_zfmisc_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,k3_tarski(B_29))
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [A_28,A_13] :
      ( r1_tarski(A_28,A_13)
      | ~ r2_hidden(A_28,k1_zfmisc_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_62])).

tff(c_192,plain,(
    ! [B_57,A_13] :
      ( r1_tarski(B_57,A_13)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_185,c_65])).

tff(c_197,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_192])).

tff(c_210,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_197])).

tff(c_36,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_67,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_30,plain,
    ( ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_69,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_30])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_110,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k3_subset_1(A_43,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_122,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_110])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_xboole_0(A_40,C_41)
      | ~ r1_xboole_0(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_144,plain,(
    ! [A_45,B_46,A_47] :
      ( r1_xboole_0(A_45,B_46)
      | ~ r1_tarski(A_45,k4_xboole_0(A_47,B_46)) ) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_163,plain,(
    ! [A_52] :
      ( r1_xboole_0(A_52,'#skF_3')
      | ~ r1_tarski(A_52,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_144])).

tff(c_166,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_67,c_163])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_166])).

tff(c_171,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_235,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k3_subset_1(A_70,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_247,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_235])).

tff(c_259,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(A_72,k4_xboole_0(B_73,C_74))
      | ~ r1_xboole_0(A_72,C_74)
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_325,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_xboole_0(A_84,'#skF_3')
      | ~ r1_tarski(A_84,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_259])).

tff(c_174,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_30])).

tff(c_333,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_325,c_174])).

tff(c_339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_171,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  
% 2.23/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.23/1.27  
% 2.23/1.27  %Foreground sorts:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Background operators:
% 2.23/1.27  
% 2.23/1.27  
% 2.23/1.27  %Foreground operators:
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.23/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.23/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.27  
% 2.23/1.28  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.23/1.28  tff(f_67, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.23/1.28  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.23/1.28  tff(f_47, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.23/1.28  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.23/1.28  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.23/1.28  tff(f_35, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.23/1.28  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.23/1.28  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.23/1.28  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.23/1.28  tff(c_24, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.23/1.28  tff(c_185, plain, (![B_57, A_58]: (r2_hidden(B_57, A_58) | ~m1_subset_1(B_57, A_58) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.28  tff(c_12, plain, (![A_13]: (k3_tarski(k1_zfmisc_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.28  tff(c_62, plain, (![A_28, B_29]: (r1_tarski(A_28, k3_tarski(B_29)) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.28  tff(c_65, plain, (![A_28, A_13]: (r1_tarski(A_28, A_13) | ~r2_hidden(A_28, k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_62])).
% 2.23/1.28  tff(c_192, plain, (![B_57, A_13]: (r1_tarski(B_57, A_13) | ~m1_subset_1(B_57, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_185, c_65])).
% 2.23/1.28  tff(c_197, plain, (![B_59, A_60]: (r1_tarski(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)))), inference(negUnitSimplification, [status(thm)], [c_24, c_192])).
% 2.23/1.28  tff(c_210, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_197])).
% 2.23/1.28  tff(c_36, plain, (r1_xboole_0('#skF_2', '#skF_3') | r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.23/1.28  tff(c_67, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.23/1.28  tff(c_30, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.23/1.28  tff(c_69, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_30])).
% 2.23/1.28  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.23/1.28  tff(c_110, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k3_subset_1(A_43, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.28  tff(c_122, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_110])).
% 2.23/1.28  tff(c_6, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.28  tff(c_106, plain, (![A_40, C_41, B_42]: (r1_xboole_0(A_40, C_41) | ~r1_xboole_0(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.28  tff(c_144, plain, (![A_45, B_46, A_47]: (r1_xboole_0(A_45, B_46) | ~r1_tarski(A_45, k4_xboole_0(A_47, B_46)))), inference(resolution, [status(thm)], [c_6, c_106])).
% 2.23/1.28  tff(c_163, plain, (![A_52]: (r1_xboole_0(A_52, '#skF_3') | ~r1_tarski(A_52, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_122, c_144])).
% 2.23/1.28  tff(c_166, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_67, c_163])).
% 2.23/1.28  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_166])).
% 2.23/1.28  tff(c_171, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_36])).
% 2.23/1.28  tff(c_235, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k3_subset_1(A_70, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.23/1.28  tff(c_247, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_235])).
% 2.23/1.28  tff(c_259, plain, (![A_72, B_73, C_74]: (r1_tarski(A_72, k4_xboole_0(B_73, C_74)) | ~r1_xboole_0(A_72, C_74) | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.23/1.28  tff(c_325, plain, (![A_84]: (r1_tarski(A_84, k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0(A_84, '#skF_3') | ~r1_tarski(A_84, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_247, c_259])).
% 2.23/1.28  tff(c_174, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_30])).
% 2.23/1.28  tff(c_333, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_325, c_174])).
% 2.23/1.28  tff(c_339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_171, c_333])).
% 2.23/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  Inference rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Ref     : 0
% 2.23/1.28  #Sup     : 71
% 2.23/1.28  #Fact    : 0
% 2.23/1.28  #Define  : 0
% 2.23/1.28  #Split   : 2
% 2.23/1.28  #Chain   : 0
% 2.23/1.28  #Close   : 0
% 2.23/1.28  
% 2.23/1.28  Ordering : KBO
% 2.23/1.28  
% 2.23/1.28  Simplification rules
% 2.23/1.28  ----------------------
% 2.23/1.28  #Subsume      : 12
% 2.23/1.28  #Demod        : 6
% 2.23/1.28  #Tautology    : 25
% 2.23/1.28  #SimpNegUnit  : 4
% 2.23/1.28  #BackRed      : 0
% 2.23/1.28  
% 2.23/1.28  #Partial instantiations: 0
% 2.23/1.28  #Strategies tried      : 1
% 2.23/1.28  
% 2.23/1.28  Timing (in seconds)
% 2.23/1.28  ----------------------
% 2.23/1.29  Preprocessing        : 0.29
% 2.23/1.29  Parsing              : 0.15
% 2.23/1.29  CNF conversion       : 0.02
% 2.23/1.29  Main loop            : 0.24
% 2.23/1.29  Inferencing          : 0.10
% 2.23/1.29  Reduction            : 0.07
% 2.23/1.29  Demodulation         : 0.05
% 2.23/1.29  BG Simplification    : 0.01
% 2.23/1.29  Subsumption          : 0.05
% 2.23/1.29  Abstraction          : 0.01
% 2.23/1.29  MUC search           : 0.00
% 2.23/1.29  Cooper               : 0.00
% 2.23/1.29  Total                : 0.56
% 2.23/1.29  Index Insertion      : 0.00
% 2.23/1.29  Index Deletion       : 0.00
% 2.23/1.29  Index Matching       : 0.00
% 2.23/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
