%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:47 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   58 (  75 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 ( 119 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_28,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,(
    ! [A_15] : ~ v1_subset_1(k2_subset_1(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    ! [A_15] : ~ v1_subset_1(A_15,A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_67,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [D_10,B_6] : r2_hidden(D_10,k2_tarski(D_10,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_61,plain,(
    ! [B_30,A_31] :
      ( ~ r2_hidden(B_30,A_31)
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [D_10,B_6] : ~ v1_xboole_0(k2_tarski(D_10,B_6)) ),
    inference(resolution,[status(thm)],[c_10,c_61])).

tff(c_72,plain,(
    ! [A_34] : ~ v1_xboole_0(k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_65])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_150,plain,(
    ! [A_51,B_52] :
      ( k6_domain_1(A_51,B_52) = k1_tarski(B_52)
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_156,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_150])).

tff(c_160,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_156])).

tff(c_241,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k6_domain_1(A_56,B_57),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_250,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_241])).

tff(c_254,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_250])).

tff(c_255,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_254])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_264,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_255,c_32])).

tff(c_40,plain,(
    ! [B_24,A_22] :
      ( B_24 = A_22
      | ~ r1_tarski(A_22,B_24)
      | ~ v1_zfmisc_1(B_24)
      | v1_xboole_0(B_24)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_267,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_264,c_40])).

tff(c_270,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_267])).

tff(c_271,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_48,c_270])).

tff(c_44,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_175,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_44])).

tff(c_274,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_175])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_274])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:29:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.37  
% 2.01/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.38  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.01/1.38  
% 2.01/1.38  %Foreground sorts:
% 2.01/1.38  
% 2.01/1.38  
% 2.01/1.38  %Background operators:
% 2.01/1.38  
% 2.01/1.38  
% 2.01/1.38  %Foreground operators:
% 2.01/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.38  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.01/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.01/1.38  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.01/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.01/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.01/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.38  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.01/1.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.01/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.01/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.38  
% 2.01/1.39  tff(f_46, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.01/1.39  tff(f_49, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.01/1.39  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.01/1.39  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.01/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.01/1.39  tff(f_92, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.01/1.39  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.01/1.39  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.01/1.39  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.01/1.39  tff(f_80, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.01/1.39  tff(c_28, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.01/1.39  tff(c_30, plain, (![A_15]: (~v1_subset_1(k2_subset_1(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.01/1.39  tff(c_49, plain, (![A_15]: (~v1_subset_1(A_15, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 2.01/1.39  tff(c_67, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.01/1.39  tff(c_10, plain, (![D_10, B_6]: (r2_hidden(D_10, k2_tarski(D_10, B_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.01/1.39  tff(c_61, plain, (![B_30, A_31]: (~r2_hidden(B_30, A_31) | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.39  tff(c_65, plain, (![D_10, B_6]: (~v1_xboole_0(k2_tarski(D_10, B_6)))), inference(resolution, [status(thm)], [c_10, c_61])).
% 2.01/1.39  tff(c_72, plain, (![A_34]: (~v1_xboole_0(k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_65])).
% 2.01/1.39  tff(c_48, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.01/1.39  tff(c_42, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.01/1.39  tff(c_46, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.01/1.39  tff(c_150, plain, (![A_51, B_52]: (k6_domain_1(A_51, B_52)=k1_tarski(B_52) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.01/1.39  tff(c_156, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_150])).
% 2.01/1.39  tff(c_160, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_48, c_156])).
% 2.01/1.39  tff(c_241, plain, (![A_56, B_57]: (m1_subset_1(k6_domain_1(A_56, B_57), k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.01/1.39  tff(c_250, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_160, c_241])).
% 2.01/1.39  tff(c_254, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_250])).
% 2.01/1.39  tff(c_255, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_254])).
% 2.01/1.39  tff(c_32, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.01/1.39  tff(c_264, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_255, c_32])).
% 2.01/1.39  tff(c_40, plain, (![B_24, A_22]: (B_24=A_22 | ~r1_tarski(A_22, B_24) | ~v1_zfmisc_1(B_24) | v1_xboole_0(B_24) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.01/1.39  tff(c_267, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_264, c_40])).
% 2.01/1.39  tff(c_270, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_267])).
% 2.01/1.39  tff(c_271, plain, (k1_tarski('#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_72, c_48, c_270])).
% 2.01/1.39  tff(c_44, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.01/1.39  tff(c_175, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_44])).
% 2.01/1.39  tff(c_274, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_175])).
% 2.01/1.39  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_274])).
% 2.01/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.39  
% 2.01/1.39  Inference rules
% 2.01/1.39  ----------------------
% 2.01/1.39  #Ref     : 0
% 2.01/1.39  #Sup     : 45
% 2.01/1.39  #Fact    : 2
% 2.01/1.39  #Define  : 0
% 2.01/1.39  #Split   : 0
% 2.01/1.39  #Chain   : 0
% 2.01/1.39  #Close   : 0
% 2.01/1.39  
% 2.01/1.39  Ordering : KBO
% 2.01/1.39  
% 2.01/1.39  Simplification rules
% 2.01/1.39  ----------------------
% 2.01/1.39  #Subsume      : 6
% 2.01/1.39  #Demod        : 22
% 2.01/1.39  #Tautology    : 27
% 2.01/1.39  #SimpNegUnit  : 9
% 2.01/1.39  #BackRed      : 5
% 2.01/1.39  
% 2.01/1.39  #Partial instantiations: 0
% 2.01/1.39  #Strategies tried      : 1
% 2.01/1.39  
% 2.01/1.39  Timing (in seconds)
% 2.01/1.39  ----------------------
% 2.01/1.39  Preprocessing        : 0.30
% 2.01/1.39  Parsing              : 0.15
% 2.01/1.39  CNF conversion       : 0.02
% 2.01/1.39  Main loop            : 0.16
% 2.01/1.39  Inferencing          : 0.06
% 2.01/1.39  Reduction            : 0.05
% 2.01/1.39  Demodulation         : 0.04
% 2.01/1.39  BG Simplification    : 0.02
% 2.01/1.39  Subsumption          : 0.03
% 2.01/1.39  Abstraction          : 0.01
% 2.01/1.39  MUC search           : 0.00
% 2.01/1.39  Cooper               : 0.00
% 2.01/1.39  Total                : 0.49
% 2.01/1.39  Index Insertion      : 0.00
% 2.01/1.39  Index Deletion       : 0.00
% 2.01/1.39  Index Matching       : 0.00
% 2.01/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
