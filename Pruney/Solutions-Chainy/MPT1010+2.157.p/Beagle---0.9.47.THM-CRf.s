%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:26 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 119 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 271 expanded)
%              Number of equality atoms :   24 (  58 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_40,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_358,plain,(
    ! [D_96,C_97,B_98,A_99] :
      ( r2_hidden(k1_funct_1(D_96,C_97),B_98)
      | k1_xboole_0 = B_98
      | ~ r2_hidden(C_97,A_99)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(A_99,B_98)))
      | ~ v1_funct_2(D_96,A_99,B_98)
      | ~ v1_funct_1(D_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_371,plain,(
    ! [D_100,B_101] :
      ( r2_hidden(k1_funct_1(D_100,'#skF_5'),B_101)
      | k1_xboole_0 = B_101
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_101)))
      | ~ v1_funct_2(D_100,'#skF_3',B_101)
      | ~ v1_funct_1(D_100) ) ),
    inference(resolution,[status(thm)],[c_42,c_358])).

tff(c_374,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_371])).

tff(c_381,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_374])).

tff(c_389,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_18,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [A_34,C_35,B_36] :
      ( r2_hidden(A_34,C_35)
      | ~ r1_tarski(k2_tarski(A_34,B_36),C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_100,plain,(
    ! [A_7,C_35] :
      ( r2_hidden(A_7,C_35)
      | ~ r1_tarski(k1_tarski(A_7),C_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_97])).

tff(c_413,plain,(
    ! [C_35] :
      ( r2_hidden('#skF_4',C_35)
      | ~ r1_tarski(k1_xboole_0,C_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_100])).

tff(c_430,plain,(
    ! [C_105] : r2_hidden('#skF_4',C_105) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_413])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_186,plain,(
    ! [D_67,C_68,B_69,A_70] :
      ( r2_hidden(k1_funct_1(D_67,C_68),B_69)
      | k1_xboole_0 = B_69
      | ~ r2_hidden(C_68,A_70)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(A_70,B_69)))
      | ~ v1_funct_2(D_67,A_70,B_69)
      | ~ v1_funct_1(D_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_199,plain,(
    ! [D_71,B_72] :
      ( r2_hidden(k1_funct_1(D_71,'#skF_5'),B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_72)))
      | ~ v1_funct_2(D_71,'#skF_3',B_72)
      | ~ v1_funct_1(D_71) ) ),
    inference(resolution,[status(thm)],[c_42,c_186])).

tff(c_202,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_199])).

tff(c_209,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_202])).

tff(c_211,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_117,plain,(
    ! [C_44,B_45,A_46] :
      ( ~ v1_xboole_0(C_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_120,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
      | ~ r2_hidden(A_46,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_117])).

tff(c_121,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_212,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_121])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26,c_212])).

tff(c_218,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_6,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_224,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_218,c_6])).

tff(c_229,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_224])).

tff(c_230,plain,(
    ! [A_46] : ~ r2_hidden(A_46,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_442,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_430,c_230])).

tff(c_443,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_449,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_443,c_6])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_449])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.75  
% 2.95/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.75  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.95/1.75  
% 2.95/1.75  %Foreground sorts:
% 2.95/1.75  
% 2.95/1.75  
% 2.95/1.75  %Background operators:
% 2.95/1.75  
% 2.95/1.75  
% 2.95/1.75  %Foreground operators:
% 2.95/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.95/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.95/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.75  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.95/1.75  tff('#skF_6', type, '#skF_6': $i).
% 2.95/1.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.95/1.75  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.95/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.75  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.95/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.95/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.76  
% 3.18/1.78  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.18/1.78  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.18/1.78  tff(f_72, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.18/1.78  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.18/1.78  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.18/1.78  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.18/1.78  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.18/1.78  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.18/1.78  tff(f_35, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.18/1.78  tff(c_40, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.18/1.78  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.18/1.78  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.18/1.78  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.18/1.78  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.18/1.78  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.18/1.78  tff(c_358, plain, (![D_96, C_97, B_98, A_99]: (r2_hidden(k1_funct_1(D_96, C_97), B_98) | k1_xboole_0=B_98 | ~r2_hidden(C_97, A_99) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(A_99, B_98))) | ~v1_funct_2(D_96, A_99, B_98) | ~v1_funct_1(D_96))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.18/1.78  tff(c_371, plain, (![D_100, B_101]: (r2_hidden(k1_funct_1(D_100, '#skF_5'), B_101) | k1_xboole_0=B_101 | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_101))) | ~v1_funct_2(D_100, '#skF_3', B_101) | ~v1_funct_1(D_100))), inference(resolution, [status(thm)], [c_42, c_358])).
% 3.18/1.78  tff(c_374, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_371])).
% 3.18/1.78  tff(c_381, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_374])).
% 3.18/1.78  tff(c_389, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_381])).
% 3.18/1.78  tff(c_18, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.78  tff(c_97, plain, (![A_34, C_35, B_36]: (r2_hidden(A_34, C_35) | ~r1_tarski(k2_tarski(A_34, B_36), C_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.18/1.78  tff(c_100, plain, (![A_7, C_35]: (r2_hidden(A_7, C_35) | ~r1_tarski(k1_tarski(A_7), C_35))), inference(superposition, [status(thm), theory('equality')], [c_18, c_97])).
% 3.18/1.78  tff(c_413, plain, (![C_35]: (r2_hidden('#skF_4', C_35) | ~r1_tarski(k1_xboole_0, C_35))), inference(superposition, [status(thm), theory('equality')], [c_389, c_100])).
% 3.18/1.78  tff(c_430, plain, (![C_105]: (r2_hidden('#skF_4', C_105))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_413])).
% 3.18/1.78  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.18/1.78  tff(c_26, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.18/1.78  tff(c_186, plain, (![D_67, C_68, B_69, A_70]: (r2_hidden(k1_funct_1(D_67, C_68), B_69) | k1_xboole_0=B_69 | ~r2_hidden(C_68, A_70) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(A_70, B_69))) | ~v1_funct_2(D_67, A_70, B_69) | ~v1_funct_1(D_67))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.18/1.78  tff(c_199, plain, (![D_71, B_72]: (r2_hidden(k1_funct_1(D_71, '#skF_5'), B_72) | k1_xboole_0=B_72 | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_72))) | ~v1_funct_2(D_71, '#skF_3', B_72) | ~v1_funct_1(D_71))), inference(resolution, [status(thm)], [c_42, c_186])).
% 3.18/1.78  tff(c_202, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_199])).
% 3.18/1.78  tff(c_209, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_202])).
% 3.18/1.78  tff(c_211, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_209])).
% 3.18/1.78  tff(c_117, plain, (![C_44, B_45, A_46]: (~v1_xboole_0(C_44) | ~m1_subset_1(B_45, k1_zfmisc_1(C_44)) | ~r2_hidden(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.18/1.78  tff(c_120, plain, (![A_46]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | ~r2_hidden(A_46, '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_117])).
% 3.18/1.78  tff(c_121, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(splitLeft, [status(thm)], [c_120])).
% 3.18/1.78  tff(c_212, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_121])).
% 3.18/1.78  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_26, c_212])).
% 3.18/1.78  tff(c_218, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_209])).
% 3.18/1.78  tff(c_6, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.18/1.78  tff(c_224, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_218, c_6])).
% 3.18/1.78  tff(c_229, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_224])).
% 3.18/1.78  tff(c_230, plain, (![A_46]: (~r2_hidden(A_46, '#skF_6'))), inference(splitRight, [status(thm)], [c_120])).
% 3.18/1.78  tff(c_442, plain, $false, inference(resolution, [status(thm)], [c_430, c_230])).
% 3.18/1.78  tff(c_443, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_381])).
% 3.18/1.78  tff(c_449, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_443, c_6])).
% 3.18/1.78  tff(c_454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_449])).
% 3.18/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.78  
% 3.18/1.78  Inference rules
% 3.18/1.78  ----------------------
% 3.18/1.78  #Ref     : 0
% 3.18/1.78  #Sup     : 86
% 3.18/1.78  #Fact    : 0
% 3.18/1.78  #Define  : 0
% 3.18/1.78  #Split   : 3
% 3.18/1.78  #Chain   : 0
% 3.18/1.78  #Close   : 0
% 3.18/1.78  
% 3.18/1.78  Ordering : KBO
% 3.18/1.78  
% 3.18/1.78  Simplification rules
% 3.18/1.78  ----------------------
% 3.18/1.78  #Subsume      : 4
% 3.18/1.78  #Demod        : 38
% 3.18/1.78  #Tautology    : 50
% 3.18/1.78  #SimpNegUnit  : 3
% 3.18/1.78  #BackRed      : 6
% 3.18/1.78  
% 3.18/1.78  #Partial instantiations: 0
% 3.18/1.78  #Strategies tried      : 1
% 3.18/1.78  
% 3.18/1.78  Timing (in seconds)
% 3.18/1.78  ----------------------
% 3.18/1.78  Preprocessing        : 0.47
% 3.18/1.78  Parsing              : 0.24
% 3.18/1.78  CNF conversion       : 0.03
% 3.18/1.78  Main loop            : 0.42
% 3.18/1.78  Inferencing          : 0.15
% 3.18/1.78  Reduction            : 0.12
% 3.18/1.78  Demodulation         : 0.09
% 3.18/1.78  BG Simplification    : 0.03
% 3.18/1.78  Subsumption          : 0.09
% 3.18/1.78  Abstraction          : 0.03
% 3.18/1.78  MUC search           : 0.00
% 3.18/1.78  Cooper               : 0.00
% 3.18/1.78  Total                : 0.94
% 3.18/1.78  Index Insertion      : 0.00
% 3.18/1.78  Index Deletion       : 0.00
% 3.18/1.78  Index Matching       : 0.00
% 3.18/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
