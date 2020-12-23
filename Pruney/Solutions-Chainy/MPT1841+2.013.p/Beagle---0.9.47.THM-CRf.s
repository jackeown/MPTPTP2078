%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:29 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 128 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   79 ( 238 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_60,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_64,plain,(
    m1_subset_1('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_180,plain,(
    ! [A_67,B_68] :
      ( k6_domain_1(A_67,B_68) = k1_tarski(B_68)
      | ~ m1_subset_1(B_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_183,plain,
    ( k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_180])).

tff(c_186,plain,(
    k6_domain_1('#skF_5','#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_183])).

tff(c_62,plain,(
    v1_subset_1(k6_domain_1('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_187,plain,(
    v1_subset_1(k1_tarski('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_62])).

tff(c_192,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k6_domain_1(A_69,B_70),k1_zfmisc_1(A_69))
      | ~ m1_subset_1(B_70,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_201,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_192])).

tff(c_205,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_201])).

tff(c_206,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_205])).

tff(c_342,plain,(
    ! [B_83,A_84] :
      ( ~ v1_subset_1(B_83,A_84)
      | v1_xboole_0(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_zfmisc_1(A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_345,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_6'),'#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6'))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_206,c_342])).

tff(c_351,plain,
    ( v1_xboole_0(k1_tarski('#skF_6'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_187,c_345])).

tff(c_352,plain,(
    v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_351])).

tff(c_20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_95,plain,(
    ! [B_41,A_42] :
      ( ~ v1_xboole_0(B_41)
      | B_41 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_98,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_20,c_95])).

tff(c_359,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_352,c_98])).

tff(c_77,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [D_17,B_13] : r2_hidden(D_17,k2_tarski(D_17,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_83,plain,(
    ! [A_37] : r2_hidden(A_37,k1_tarski(A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_32])).

tff(c_375,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_83])).

tff(c_24,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_116,plain,(
    ! [D_50,B_51,A_52] :
      ( ~ r2_hidden(D_50,B_51)
      | ~ r2_hidden(D_50,k4_xboole_0(A_52,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_123,plain,(
    ! [D_50,A_9] :
      ( ~ r2_hidden(D_50,k1_xboole_0)
      | ~ r2_hidden(D_50,A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_116])).

tff(c_400,plain,(
    ! [A_9] : ~ r2_hidden('#skF_6',A_9) ),
    inference(resolution,[status(thm)],[c_375,c_123])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:21:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.33  
% 2.52/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.33  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.52/1.33  
% 2.52/1.33  %Foreground sorts:
% 2.52/1.33  
% 2.52/1.33  
% 2.52/1.33  %Background operators:
% 2.52/1.33  
% 2.52/1.33  
% 2.52/1.33  %Foreground operators:
% 2.52/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.52/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.33  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.52/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.33  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.52/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.52/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.52/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.52/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.52/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.52/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.52/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.52/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.33  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.52/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.52/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.52/1.33  
% 2.52/1.34  tff(f_114, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.52/1.34  tff(f_88, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.52/1.34  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.52/1.34  tff(f_102, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.52/1.34  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.52/1.34  tff(f_48, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.52/1.34  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.52/1.34  tff(f_57, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.52/1.34  tff(f_40, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.52/1.34  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.52/1.34  tff(c_66, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.52/1.34  tff(c_60, plain, (v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.52/1.34  tff(c_64, plain, (m1_subset_1('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.52/1.34  tff(c_180, plain, (![A_67, B_68]: (k6_domain_1(A_67, B_68)=k1_tarski(B_68) | ~m1_subset_1(B_68, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.52/1.34  tff(c_183, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_64, c_180])).
% 2.52/1.34  tff(c_186, plain, (k6_domain_1('#skF_5', '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_66, c_183])).
% 2.52/1.34  tff(c_62, plain, (v1_subset_1(k6_domain_1('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.52/1.34  tff(c_187, plain, (v1_subset_1(k1_tarski('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_62])).
% 2.52/1.34  tff(c_192, plain, (![A_69, B_70]: (m1_subset_1(k6_domain_1(A_69, B_70), k1_zfmisc_1(A_69)) | ~m1_subset_1(B_70, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.52/1.34  tff(c_201, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', '#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_186, c_192])).
% 2.52/1.34  tff(c_205, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_201])).
% 2.52/1.34  tff(c_206, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_66, c_205])).
% 2.52/1.34  tff(c_342, plain, (![B_83, A_84]: (~v1_subset_1(B_83, A_84) | v1_xboole_0(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_zfmisc_1(A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.52/1.34  tff(c_345, plain, (~v1_subset_1(k1_tarski('#skF_6'), '#skF_5') | v1_xboole_0(k1_tarski('#skF_6')) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_206, c_342])).
% 2.52/1.34  tff(c_351, plain, (v1_xboole_0(k1_tarski('#skF_6')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_187, c_345])).
% 2.52/1.34  tff(c_352, plain, (v1_xboole_0(k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_66, c_351])).
% 2.52/1.34  tff(c_20, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.52/1.34  tff(c_95, plain, (![B_41, A_42]: (~v1_xboole_0(B_41) | B_41=A_42 | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.52/1.34  tff(c_98, plain, (![A_42]: (k1_xboole_0=A_42 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_20, c_95])).
% 2.52/1.34  tff(c_359, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_352, c_98])).
% 2.52/1.34  tff(c_77, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.52/1.34  tff(c_32, plain, (![D_17, B_13]: (r2_hidden(D_17, k2_tarski(D_17, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.52/1.34  tff(c_83, plain, (![A_37]: (r2_hidden(A_37, k1_tarski(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_32])).
% 2.52/1.34  tff(c_375, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_359, c_83])).
% 2.52/1.34  tff(c_24, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.52/1.34  tff(c_116, plain, (![D_50, B_51, A_52]: (~r2_hidden(D_50, B_51) | ~r2_hidden(D_50, k4_xboole_0(A_52, B_51)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.52/1.34  tff(c_123, plain, (![D_50, A_9]: (~r2_hidden(D_50, k1_xboole_0) | ~r2_hidden(D_50, A_9))), inference(superposition, [status(thm), theory('equality')], [c_24, c_116])).
% 2.52/1.34  tff(c_400, plain, (![A_9]: (~r2_hidden('#skF_6', A_9))), inference(resolution, [status(thm)], [c_375, c_123])).
% 2.52/1.34  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_400, c_375])).
% 2.52/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.34  
% 2.52/1.34  Inference rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Ref     : 0
% 2.52/1.34  #Sup     : 72
% 2.52/1.34  #Fact    : 0
% 2.52/1.34  #Define  : 0
% 2.52/1.34  #Split   : 1
% 2.52/1.34  #Chain   : 0
% 2.52/1.34  #Close   : 0
% 2.52/1.35  
% 2.52/1.35  Ordering : KBO
% 2.52/1.35  
% 2.52/1.35  Simplification rules
% 2.52/1.35  ----------------------
% 2.52/1.35  #Subsume      : 4
% 2.52/1.35  #Demod        : 39
% 2.52/1.35  #Tautology    : 39
% 2.52/1.35  #SimpNegUnit  : 9
% 2.52/1.35  #BackRed      : 13
% 2.52/1.35  
% 2.52/1.35  #Partial instantiations: 0
% 2.52/1.35  #Strategies tried      : 1
% 2.52/1.35  
% 2.52/1.35  Timing (in seconds)
% 2.52/1.35  ----------------------
% 2.52/1.35  Preprocessing        : 0.34
% 2.52/1.35  Parsing              : 0.17
% 2.52/1.35  CNF conversion       : 0.03
% 2.52/1.35  Main loop            : 0.25
% 2.52/1.35  Inferencing          : 0.09
% 2.52/1.35  Reduction            : 0.08
% 2.52/1.35  Demodulation         : 0.06
% 2.52/1.35  BG Simplification    : 0.02
% 2.52/1.35  Subsumption          : 0.05
% 2.52/1.35  Abstraction          : 0.02
% 2.52/1.35  MUC search           : 0.00
% 2.52/1.35  Cooper               : 0.00
% 2.52/1.35  Total                : 0.63
% 2.52/1.35  Index Insertion      : 0.00
% 2.52/1.35  Index Deletion       : 0.00
% 2.52/1.35  Index Matching       : 0.00
% 2.52/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
