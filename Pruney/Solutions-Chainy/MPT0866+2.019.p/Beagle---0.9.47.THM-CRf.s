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
% DateTime   : Thu Dec  3 10:09:22 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 102 expanded)
%              Number of equality atoms :   32 (  50 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_37,plain,(
    ! [A_19,B_20] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_19,B_20)),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    ! [A_19] : k2_relat_1(k2_zfmisc_1(A_19,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_6])).

tff(c_58,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(k2_relat_1(A_22))
      | ~ v1_relat_1(A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(A_19,k1_xboole_0))
      | v1_xboole_0(k2_zfmisc_1(A_19,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_58])).

tff(c_64,plain,(
    ! [A_23] : v1_xboole_0(k2_zfmisc_1(A_23,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2,c_61])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_68,plain,(
    ! [A_23] : k2_zfmisc_1(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_4])).

tff(c_70,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_42])).

tff(c_22,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_267,plain,(
    ! [A_283,B_284] :
      ( k4_tarski(k1_mcart_1(A_283),k2_mcart_1(A_283)) = A_283
      | ~ r2_hidden(A_283,B_284)
      | ~ v1_relat_1(B_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_271,plain,(
    ! [A_285,B_286] :
      ( k4_tarski(k1_mcart_1(A_285),k2_mcart_1(A_285)) = A_285
      | ~ v1_relat_1(B_286)
      | v1_xboole_0(B_286)
      | ~ m1_subset_1(A_285,B_286) ) ),
    inference(resolution,[status(thm)],[c_8,c_267])).

tff(c_273,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_271])).

tff(c_276,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_273])).

tff(c_277,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_276])).

tff(c_281,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_277,c_4])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k2_relat_1(k2_zfmisc_1(A_10,B_11)) = B_11
      | k1_xboole_0 = B_11
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_291,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_16])).

tff(c_300,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_291])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_26,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:43:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.98/1.23  
% 1.98/1.23  %Foreground sorts:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Background operators:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Foreground operators:
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.98/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.23  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.98/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.23  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.98/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.23  
% 2.02/1.24  tff(f_84, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_mcart_1)).
% 2.02/1.24  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.02/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.02/1.24  tff(f_52, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 2.02/1.24  tff(f_34, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.02/1.24  tff(f_50, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.02/1.24  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.02/1.24  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.02/1.24  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 2.02/1.24  tff(f_64, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 2.02/1.24  tff(c_28, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.24  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.24  tff(c_10, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.02/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.02/1.24  tff(c_37, plain, (![A_19, B_20]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_19, B_20)), B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.02/1.24  tff(c_6, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.24  tff(c_42, plain, (![A_19]: (k2_relat_1(k2_zfmisc_1(A_19, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_37, c_6])).
% 2.02/1.24  tff(c_58, plain, (![A_22]: (~v1_xboole_0(k2_relat_1(A_22)) | ~v1_relat_1(A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.02/1.24  tff(c_61, plain, (![A_19]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(A_19, k1_xboole_0)) | v1_xboole_0(k2_zfmisc_1(A_19, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_58])).
% 2.02/1.24  tff(c_64, plain, (![A_23]: (v1_xboole_0(k2_zfmisc_1(A_23, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2, c_61])).
% 2.02/1.24  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.02/1.24  tff(c_68, plain, (![A_23]: (k2_zfmisc_1(A_23, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_4])).
% 2.02/1.24  tff(c_70, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_42])).
% 2.02/1.24  tff(c_22, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.24  tff(c_24, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.24  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.02/1.24  tff(c_267, plain, (![A_283, B_284]: (k4_tarski(k1_mcart_1(A_283), k2_mcart_1(A_283))=A_283 | ~r2_hidden(A_283, B_284) | ~v1_relat_1(B_284))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.02/1.24  tff(c_271, plain, (![A_285, B_286]: (k4_tarski(k1_mcart_1(A_285), k2_mcart_1(A_285))=A_285 | ~v1_relat_1(B_286) | v1_xboole_0(B_286) | ~m1_subset_1(A_285, B_286))), inference(resolution, [status(thm)], [c_8, c_267])).
% 2.02/1.24  tff(c_273, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_271])).
% 2.02/1.24  tff(c_276, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_273])).
% 2.02/1.24  tff(c_277, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_22, c_276])).
% 2.02/1.24  tff(c_281, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_277, c_4])).
% 2.02/1.24  tff(c_16, plain, (![A_10, B_11]: (k2_relat_1(k2_zfmisc_1(A_10, B_11))=B_11 | k1_xboole_0=B_11 | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.02/1.24  tff(c_291, plain, (k2_relat_1(k1_xboole_0)='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_281, c_16])).
% 2.02/1.24  tff(c_300, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_291])).
% 2.02/1.24  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_26, c_300])).
% 2.02/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.24  
% 2.02/1.24  Inference rules
% 2.02/1.24  ----------------------
% 2.02/1.24  #Ref     : 0
% 2.02/1.24  #Sup     : 82
% 2.02/1.24  #Fact    : 0
% 2.02/1.24  #Define  : 0
% 2.02/1.24  #Split   : 1
% 2.02/1.24  #Chain   : 0
% 2.02/1.24  #Close   : 0
% 2.02/1.24  
% 2.02/1.24  Ordering : KBO
% 2.02/1.24  
% 2.02/1.24  Simplification rules
% 2.02/1.24  ----------------------
% 2.02/1.24  #Subsume      : 8
% 2.02/1.24  #Demod        : 19
% 2.02/1.24  #Tautology    : 21
% 2.02/1.24  #SimpNegUnit  : 3
% 2.02/1.24  #BackRed      : 4
% 2.02/1.24  
% 2.02/1.24  #Partial instantiations: 56
% 2.02/1.24  #Strategies tried      : 1
% 2.02/1.24  
% 2.02/1.24  Timing (in seconds)
% 2.02/1.24  ----------------------
% 2.02/1.24  Preprocessing        : 0.27
% 2.02/1.24  Parsing              : 0.15
% 2.02/1.24  CNF conversion       : 0.02
% 2.02/1.24  Main loop            : 0.19
% 2.02/1.24  Inferencing          : 0.09
% 2.02/1.24  Reduction            : 0.05
% 2.02/1.25  Demodulation         : 0.04
% 2.02/1.25  BG Simplification    : 0.01
% 2.02/1.25  Subsumption          : 0.03
% 2.02/1.25  Abstraction          : 0.01
% 2.02/1.25  MUC search           : 0.00
% 2.02/1.25  Cooper               : 0.00
% 2.02/1.25  Total                : 0.49
% 2.02/1.25  Index Insertion      : 0.00
% 2.02/1.25  Index Deletion       : 0.00
% 2.02/1.25  Index Matching       : 0.00
% 2.02/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
