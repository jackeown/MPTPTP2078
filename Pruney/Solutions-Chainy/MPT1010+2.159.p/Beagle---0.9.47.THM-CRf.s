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
% DateTime   : Thu Dec  3 10:15:26 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   55 (  59 expanded)
%              Number of leaves         :   35 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  73 expanded)
%              Number of equality atoms :   23 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_40,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k4_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_91])).

tff(c_103,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_100])).

tff(c_34,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_104,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_34])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_218,plain,(
    ! [D_97,C_98,B_99,A_100] :
      ( r2_hidden(k1_funct_1(D_97,C_98),B_99)
      | k1_xboole_0 = B_99
      | ~ r2_hidden(C_98,A_100)
      | ~ m1_subset_1(D_97,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99)))
      | ~ v1_funct_2(D_97,A_100,B_99)
      | ~ v1_funct_1(D_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_231,plain,(
    ! [D_101,B_102] :
      ( r2_hidden(k1_funct_1(D_101,'#skF_5'),B_102)
      | k1_xboole_0 = B_102
      | ~ m1_subset_1(D_101,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_102)))
      | ~ v1_funct_2(D_101,'#skF_3',B_102)
      | ~ v1_funct_1(D_101) ) ),
    inference(resolution,[status(thm)],[c_42,c_218])).

tff(c_234,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_231])).

tff(c_237,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_234])).

tff(c_238,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_237])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_243,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_238,c_8])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_243])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.76  
% 2.74/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.77  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.74/1.77  
% 2.74/1.77  %Foreground sorts:
% 2.74/1.77  
% 2.74/1.77  
% 2.74/1.77  %Background operators:
% 2.74/1.77  
% 2.74/1.77  
% 2.74/1.77  %Foreground operators:
% 2.74/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.74/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.74/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.77  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.74/1.77  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.77  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.74/1.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.77  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.74/1.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.77  
% 2.74/1.79  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.74/1.79  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.74/1.79  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.74/1.79  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.74/1.79  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.74/1.79  tff(f_69, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.74/1.79  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.74/1.79  tff(c_40, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.74/1.79  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.79  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.79  tff(c_91, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k4_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.74/1.79  tff(c_100, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_91])).
% 2.74/1.79  tff(c_103, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_100])).
% 2.74/1.79  tff(c_34, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.74/1.79  tff(c_104, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_103, c_34])).
% 2.74/1.79  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.74/1.79  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.74/1.79  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.74/1.79  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.74/1.79  tff(c_218, plain, (![D_97, C_98, B_99, A_100]: (r2_hidden(k1_funct_1(D_97, C_98), B_99) | k1_xboole_0=B_99 | ~r2_hidden(C_98, A_100) | ~m1_subset_1(D_97, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))) | ~v1_funct_2(D_97, A_100, B_99) | ~v1_funct_1(D_97))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.74/1.79  tff(c_231, plain, (![D_101, B_102]: (r2_hidden(k1_funct_1(D_101, '#skF_5'), B_102) | k1_xboole_0=B_102 | ~m1_subset_1(D_101, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_102))) | ~v1_funct_2(D_101, '#skF_3', B_102) | ~v1_funct_1(D_101))), inference(resolution, [status(thm)], [c_42, c_218])).
% 2.74/1.79  tff(c_234, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_231])).
% 2.74/1.79  tff(c_237, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_234])).
% 2.74/1.79  tff(c_238, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_104, c_237])).
% 2.74/1.79  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.74/1.79  tff(c_243, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_238, c_8])).
% 2.74/1.79  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_243])).
% 2.74/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.79  
% 2.74/1.79  Inference rules
% 2.74/1.79  ----------------------
% 2.74/1.79  #Ref     : 0
% 2.74/1.79  #Sup     : 42
% 2.74/1.79  #Fact    : 0
% 2.74/1.79  #Define  : 0
% 2.74/1.79  #Split   : 0
% 2.74/1.79  #Chain   : 0
% 2.74/1.79  #Close   : 0
% 2.74/1.79  
% 2.74/1.79  Ordering : KBO
% 2.74/1.79  
% 2.74/1.79  Simplification rules
% 2.74/1.79  ----------------------
% 2.74/1.79  #Subsume      : 0
% 2.74/1.79  #Demod        : 6
% 2.74/1.79  #Tautology    : 32
% 2.74/1.79  #SimpNegUnit  : 4
% 2.74/1.79  #BackRed      : 1
% 2.74/1.79  
% 2.74/1.79  #Partial instantiations: 0
% 2.74/1.79  #Strategies tried      : 1
% 2.74/1.79  
% 2.74/1.79  Timing (in seconds)
% 2.74/1.79  ----------------------
% 2.74/1.79  Preprocessing        : 0.54
% 2.74/1.79  Parsing              : 0.27
% 2.74/1.79  CNF conversion       : 0.04
% 2.74/1.79  Main loop            : 0.32
% 2.74/1.79  Inferencing          : 0.12
% 2.74/1.79  Reduction            : 0.09
% 2.74/1.79  Demodulation         : 0.06
% 2.74/1.79  BG Simplification    : 0.03
% 2.74/1.79  Subsumption          : 0.06
% 2.74/1.79  Abstraction          : 0.02
% 2.74/1.79  MUC search           : 0.00
% 2.74/1.79  Cooper               : 0.00
% 2.74/1.79  Total                : 0.90
% 2.74/1.79  Index Insertion      : 0.00
% 2.74/1.79  Index Deletion       : 0.00
% 2.74/1.79  Index Matching       : 0.00
% 2.74/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
