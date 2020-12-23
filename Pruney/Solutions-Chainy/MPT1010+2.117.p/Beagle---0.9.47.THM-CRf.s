%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:21 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 154 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_42,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1759,plain,(
    ! [D_3219,C_3220,B_3221,A_3222] :
      ( r2_hidden(k1_funct_1(D_3219,C_3220),B_3221)
      | k1_xboole_0 = B_3221
      | ~ r2_hidden(C_3220,A_3222)
      | ~ m1_subset_1(D_3219,k1_zfmisc_1(k2_zfmisc_1(A_3222,B_3221)))
      | ~ v1_funct_2(D_3219,A_3222,B_3221)
      | ~ v1_funct_1(D_3219) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2197,plain,(
    ! [D_4057,B_4058] :
      ( r2_hidden(k1_funct_1(D_4057,'#skF_5'),B_4058)
      | k1_xboole_0 = B_4058
      | ~ m1_subset_1(D_4057,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_4058)))
      | ~ v1_funct_2(D_4057,'#skF_3',B_4058)
      | ~ v1_funct_1(D_4057) ) ),
    inference(resolution,[status(thm)],[c_44,c_1759])).

tff(c_2210,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_2197])).

tff(c_2214,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2210])).

tff(c_2215,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2214])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_62,plain,(
    ! [D_26,A_27] : r2_hidden(D_26,k2_tarski(A_27,D_26)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_62])).

tff(c_36,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,(
    ! [C_39,B_40,A_41] :
      ( ~ v1_xboole_0(C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_108,plain,(
    ! [B_42,A_43,A_44] :
      ( ~ v1_xboole_0(B_42)
      | ~ r2_hidden(A_43,A_44)
      | ~ r1_tarski(A_44,B_42) ) ),
    inference(resolution,[status(thm)],[c_36,c_101])).

tff(c_128,plain,(
    ! [B_46,A_47] :
      ( ~ v1_xboole_0(B_46)
      | ~ r1_tarski(k1_tarski(A_47),B_46) ) ),
    inference(resolution,[status(thm)],[c_65,c_108])).

tff(c_133,plain,(
    ! [A_47] : ~ v1_xboole_0(k1_tarski(A_47)) ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_2229,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2215,c_133])).

tff(c_2277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2229])).

tff(c_2278,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2214])).

tff(c_155,plain,(
    ! [D_57,B_58,A_59] :
      ( D_57 = B_58
      | D_57 = A_59
      | ~ r2_hidden(D_57,k2_tarski(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_164,plain,(
    ! [D_57,A_9] :
      ( D_57 = A_9
      | D_57 = A_9
      | ~ r2_hidden(D_57,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_155])).

tff(c_2290,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2278,c_164])).

tff(c_2337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_42,c_2290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.60  
% 3.44/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.61  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.44/1.61  
% 3.44/1.61  %Foreground sorts:
% 3.44/1.61  
% 3.44/1.61  
% 3.44/1.61  %Background operators:
% 3.44/1.61  
% 3.44/1.61  
% 3.44/1.61  %Foreground operators:
% 3.44/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.44/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.44/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.44/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.44/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.44/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.44/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.61  
% 3.44/1.62  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.44/1.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.44/1.62  tff(f_70, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.44/1.62  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.44/1.62  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.44/1.62  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.44/1.62  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.44/1.62  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.44/1.62  tff(c_42, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.44/1.62  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.62  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.62  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.62  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.44/1.62  tff(c_1759, plain, (![D_3219, C_3220, B_3221, A_3222]: (r2_hidden(k1_funct_1(D_3219, C_3220), B_3221) | k1_xboole_0=B_3221 | ~r2_hidden(C_3220, A_3222) | ~m1_subset_1(D_3219, k1_zfmisc_1(k2_zfmisc_1(A_3222, B_3221))) | ~v1_funct_2(D_3219, A_3222, B_3221) | ~v1_funct_1(D_3219))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.44/1.62  tff(c_2197, plain, (![D_4057, B_4058]: (r2_hidden(k1_funct_1(D_4057, '#skF_5'), B_4058) | k1_xboole_0=B_4058 | ~m1_subset_1(D_4057, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_4058))) | ~v1_funct_2(D_4057, '#skF_3', B_4058) | ~v1_funct_1(D_4057))), inference(resolution, [status(thm)], [c_44, c_1759])).
% 3.44/1.62  tff(c_2210, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_2197])).
% 3.44/1.62  tff(c_2214, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2210])).
% 3.44/1.62  tff(c_2215, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2214])).
% 3.44/1.62  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.62  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.62  tff(c_62, plain, (![D_26, A_27]: (r2_hidden(D_26, k2_tarski(A_27, D_26)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.62  tff(c_65, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_62])).
% 3.44/1.62  tff(c_36, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.62  tff(c_101, plain, (![C_39, B_40, A_41]: (~v1_xboole_0(C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.62  tff(c_108, plain, (![B_42, A_43, A_44]: (~v1_xboole_0(B_42) | ~r2_hidden(A_43, A_44) | ~r1_tarski(A_44, B_42))), inference(resolution, [status(thm)], [c_36, c_101])).
% 3.44/1.62  tff(c_128, plain, (![B_46, A_47]: (~v1_xboole_0(B_46) | ~r1_tarski(k1_tarski(A_47), B_46))), inference(resolution, [status(thm)], [c_65, c_108])).
% 3.44/1.62  tff(c_133, plain, (![A_47]: (~v1_xboole_0(k1_tarski(A_47)))), inference(resolution, [status(thm)], [c_8, c_128])).
% 3.44/1.62  tff(c_2229, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2215, c_133])).
% 3.44/1.62  tff(c_2277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2229])).
% 3.44/1.62  tff(c_2278, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_2214])).
% 3.44/1.62  tff(c_155, plain, (![D_57, B_58, A_59]: (D_57=B_58 | D_57=A_59 | ~r2_hidden(D_57, k2_tarski(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.62  tff(c_164, plain, (![D_57, A_9]: (D_57=A_9 | D_57=A_9 | ~r2_hidden(D_57, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_155])).
% 3.44/1.62  tff(c_2290, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_2278, c_164])).
% 3.44/1.62  tff(c_2337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_42, c_2290])).
% 3.44/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.62  
% 3.44/1.62  Inference rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Ref     : 0
% 3.44/1.62  #Sup     : 326
% 3.44/1.62  #Fact    : 8
% 3.44/1.62  #Define  : 0
% 3.44/1.62  #Split   : 10
% 3.44/1.62  #Chain   : 0
% 3.44/1.62  #Close   : 0
% 3.44/1.62  
% 3.44/1.62  Ordering : KBO
% 3.44/1.62  
% 3.44/1.62  Simplification rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Subsume      : 69
% 3.44/1.62  #Demod        : 40
% 3.44/1.62  #Tautology    : 80
% 3.44/1.62  #SimpNegUnit  : 1
% 3.44/1.62  #BackRed      : 5
% 3.44/1.62  
% 3.44/1.62  #Partial instantiations: 2772
% 3.44/1.62  #Strategies tried      : 1
% 3.44/1.62  
% 3.44/1.62  Timing (in seconds)
% 3.44/1.62  ----------------------
% 3.44/1.62  Preprocessing        : 0.31
% 3.44/1.62  Parsing              : 0.16
% 3.44/1.62  CNF conversion       : 0.02
% 3.44/1.62  Main loop            : 0.55
% 3.44/1.62  Inferencing          : 0.28
% 3.44/1.62  Reduction            : 0.12
% 3.44/1.62  Demodulation         : 0.09
% 3.44/1.62  BG Simplification    : 0.03
% 3.44/1.62  Subsumption          : 0.08
% 3.44/1.62  Abstraction          : 0.03
% 3.44/1.62  MUC search           : 0.00
% 3.44/1.62  Cooper               : 0.00
% 3.44/1.62  Total                : 0.89
% 3.44/1.62  Index Insertion      : 0.00
% 3.44/1.62  Index Deletion       : 0.00
% 3.44/1.62  Index Matching       : 0.00
% 3.44/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
