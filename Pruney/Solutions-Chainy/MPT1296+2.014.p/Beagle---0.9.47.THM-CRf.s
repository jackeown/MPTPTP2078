%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:42 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 234 expanded)
%              Number of leaves         :   24 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :   94 ( 507 expanded)
%              Number of equality atoms :   29 ( 185 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_30,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) != k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_45,plain,(
    ! [A_30,B_31] :
      ( k7_setfam_1(A_30,k7_setfam_1(A_30,B_31)) = B_31
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k7_setfam_1(A_17,B_18),k1_zfmisc_1(k1_zfmisc_1(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    ! [A_49,D_50,B_51] :
      ( r2_hidden(k3_subset_1(A_49,D_50),B_51)
      | ~ r2_hidden(D_50,k7_setfam_1(A_49,B_51))
      | ~ m1_subset_1(D_50,k1_zfmisc_1(A_49))
      | ~ m1_subset_1(k7_setfam_1(A_49,B_51),k1_zfmisc_1(k1_zfmisc_1(A_49)))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_166,plain,(
    ! [D_50] :
      ( r2_hidden(k3_subset_1('#skF_2',D_50),k7_setfam_1('#skF_2','#skF_3'))
      | ~ r2_hidden(D_50,k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_50,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_162])).

tff(c_169,plain,(
    ! [D_50] :
      ( r2_hidden(k3_subset_1('#skF_2',D_50),k7_setfam_1('#skF_2','#skF_3'))
      | ~ r2_hidden(D_50,'#skF_3')
      | ~ m1_subset_1(D_50,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48,c_166])).

tff(c_276,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_279,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_22,c_276])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_279])).

tff(c_285,plain,(
    m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( k6_setfam_1(A_23,k7_setfam_1(A_23,B_24)) = k3_subset_1(A_23,k5_setfam_1(A_23,B_24))
      | k1_xboole_0 = B_24
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_289,plain,
    ( k6_setfam_1('#skF_2',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_285,c_28])).

tff(c_301,plain,
    ( k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_289])).

tff(c_385,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_389,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_285])).

tff(c_393,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_48])).

tff(c_477,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden('#skF_1'(A_68,B_69,C_70),C_70)
      | r2_hidden(k3_subset_1(A_68,'#skF_1'(A_68,B_69,C_70)),B_69)
      | k7_setfam_1(A_68,B_69) = C_70
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_zfmisc_1(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_780,plain,(
    ! [B_89,A_90,C_91] :
      ( ~ r1_tarski(B_89,k3_subset_1(A_90,'#skF_1'(A_90,B_89,C_91)))
      | r2_hidden('#skF_1'(A_90,B_89,C_91),C_91)
      | k7_setfam_1(A_90,B_89) = C_91
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k1_zfmisc_1(A_90)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1(A_90))) ) ),
    inference(resolution,[status(thm)],[c_477,c_26])).

tff(c_785,plain,(
    ! [A_92,C_93] :
      ( r2_hidden('#skF_1'(A_92,k1_xboole_0,C_93),C_93)
      | k7_setfam_1(A_92,k1_xboole_0) = C_93
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k1_zfmisc_1(A_92)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(resolution,[status(thm)],[c_2,c_780])).

tff(c_787,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_389,c_785])).

tff(c_800,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_393,c_787])).

tff(c_801,plain,(
    r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_800])).

tff(c_810,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_801,c_26])).

tff(c_814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_810])).

tff(c_815,plain,(
    k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_53,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k5_setfam_1(A_32,B_33),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k3_subset_1(A_2,k3_subset_1(A_2,B_3)) = B_3
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_32,B_33] :
      ( k3_subset_1(A_32,k3_subset_1(A_32,k5_setfam_1(A_32,B_33))) = k5_setfam_1(A_32,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(resolution,[status(thm)],[c_53,c_4])).

tff(c_304,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))) = k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_285,c_60])).

tff(c_818,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_304])).

tff(c_820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:41:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.54  
% 3.27/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.54  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.27/1.54  
% 3.27/1.54  %Foreground sorts:
% 3.27/1.54  
% 3.27/1.54  
% 3.27/1.54  %Background operators:
% 3.27/1.54  
% 3.27/1.54  
% 3.27/1.54  %Foreground operators:
% 3.27/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.27/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.54  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 3.27/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.54  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.27/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.54  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.27/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.54  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.27/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.54  
% 3.27/1.56  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 3.27/1.56  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.27/1.56  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 3.27/1.56  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 3.27/1.56  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 3.27/1.56  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 3.27/1.56  tff(f_62, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.27/1.56  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.27/1.56  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.27/1.56  tff(c_30, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))!=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.27/1.56  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.56  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.27/1.56  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.27/1.56  tff(c_45, plain, (![A_30, B_31]: (k7_setfam_1(A_30, k7_setfam_1(A_30, B_31))=B_31 | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.27/1.56  tff(c_48, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_34, c_45])).
% 3.27/1.56  tff(c_22, plain, (![A_17, B_18]: (m1_subset_1(k7_setfam_1(A_17, B_18), k1_zfmisc_1(k1_zfmisc_1(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.27/1.56  tff(c_162, plain, (![A_49, D_50, B_51]: (r2_hidden(k3_subset_1(A_49, D_50), B_51) | ~r2_hidden(D_50, k7_setfam_1(A_49, B_51)) | ~m1_subset_1(D_50, k1_zfmisc_1(A_49)) | ~m1_subset_1(k7_setfam_1(A_49, B_51), k1_zfmisc_1(k1_zfmisc_1(A_49))) | ~m1_subset_1(B_51, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.27/1.56  tff(c_166, plain, (![D_50]: (r2_hidden(k3_subset_1('#skF_2', D_50), k7_setfam_1('#skF_2', '#skF_3')) | ~r2_hidden(D_50, k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_50, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_162])).
% 3.27/1.56  tff(c_169, plain, (![D_50]: (r2_hidden(k3_subset_1('#skF_2', D_50), k7_setfam_1('#skF_2', '#skF_3')) | ~r2_hidden(D_50, '#skF_3') | ~m1_subset_1(D_50, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48, c_166])).
% 3.27/1.56  tff(c_276, plain, (~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_169])).
% 3.27/1.56  tff(c_279, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_276])).
% 3.27/1.56  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_279])).
% 3.27/1.56  tff(c_285, plain, (m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_169])).
% 3.27/1.56  tff(c_28, plain, (![A_23, B_24]: (k6_setfam_1(A_23, k7_setfam_1(A_23, B_24))=k3_subset_1(A_23, k5_setfam_1(A_23, B_24)) | k1_xboole_0=B_24 | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_23))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.27/1.56  tff(c_289, plain, (k6_setfam_1('#skF_2', k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_285, c_28])).
% 3.27/1.56  tff(c_301, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_289])).
% 3.27/1.56  tff(c_385, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_301])).
% 3.27/1.56  tff(c_389, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_385, c_285])).
% 3.27/1.56  tff(c_393, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_385, c_48])).
% 3.27/1.56  tff(c_477, plain, (![A_68, B_69, C_70]: (r2_hidden('#skF_1'(A_68, B_69, C_70), C_70) | r2_hidden(k3_subset_1(A_68, '#skF_1'(A_68, B_69, C_70)), B_69) | k7_setfam_1(A_68, B_69)=C_70 | ~m1_subset_1(C_70, k1_zfmisc_1(k1_zfmisc_1(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.27/1.56  tff(c_26, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.27/1.56  tff(c_780, plain, (![B_89, A_90, C_91]: (~r1_tarski(B_89, k3_subset_1(A_90, '#skF_1'(A_90, B_89, C_91))) | r2_hidden('#skF_1'(A_90, B_89, C_91), C_91) | k7_setfam_1(A_90, B_89)=C_91 | ~m1_subset_1(C_91, k1_zfmisc_1(k1_zfmisc_1(A_90))) | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1(A_90))))), inference(resolution, [status(thm)], [c_477, c_26])).
% 3.27/1.56  tff(c_785, plain, (![A_92, C_93]: (r2_hidden('#skF_1'(A_92, k1_xboole_0, C_93), C_93) | k7_setfam_1(A_92, k1_xboole_0)=C_93 | ~m1_subset_1(C_93, k1_zfmisc_1(k1_zfmisc_1(A_92))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(resolution, [status(thm)], [c_2, c_780])).
% 3.27/1.56  tff(c_787, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_389, c_785])).
% 3.27/1.56  tff(c_800, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_389, c_393, c_787])).
% 3.27/1.56  tff(c_801, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_32, c_800])).
% 3.27/1.56  tff(c_810, plain, (~r1_tarski(k1_xboole_0, '#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_801, c_26])).
% 3.27/1.56  tff(c_814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_810])).
% 3.27/1.56  tff(c_815, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_301])).
% 3.27/1.56  tff(c_53, plain, (![A_32, B_33]: (m1_subset_1(k5_setfam_1(A_32, B_33), k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_32))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.27/1.56  tff(c_4, plain, (![A_2, B_3]: (k3_subset_1(A_2, k3_subset_1(A_2, B_3))=B_3 | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.56  tff(c_60, plain, (![A_32, B_33]: (k3_subset_1(A_32, k3_subset_1(A_32, k5_setfam_1(A_32, B_33)))=k5_setfam_1(A_32, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_32))))), inference(resolution, [status(thm)], [c_53, c_4])).
% 3.27/1.56  tff(c_304, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))))=k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_285, c_60])).
% 3.27/1.56  tff(c_818, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_815, c_304])).
% 3.27/1.56  tff(c_820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_818])).
% 3.27/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.56  
% 3.27/1.56  Inference rules
% 3.27/1.56  ----------------------
% 3.27/1.56  #Ref     : 0
% 3.27/1.56  #Sup     : 191
% 3.27/1.56  #Fact    : 0
% 3.27/1.56  #Define  : 0
% 3.27/1.56  #Split   : 8
% 3.27/1.56  #Chain   : 0
% 3.27/1.56  #Close   : 0
% 3.27/1.56  
% 3.27/1.56  Ordering : KBO
% 3.27/1.56  
% 3.27/1.56  Simplification rules
% 3.27/1.56  ----------------------
% 3.27/1.56  #Subsume      : 18
% 3.27/1.56  #Demod        : 109
% 3.27/1.56  #Tautology    : 76
% 3.27/1.56  #SimpNegUnit  : 7
% 3.27/1.56  #BackRed      : 12
% 3.27/1.56  
% 3.27/1.56  #Partial instantiations: 0
% 3.27/1.56  #Strategies tried      : 1
% 3.27/1.56  
% 3.27/1.56  Timing (in seconds)
% 3.27/1.56  ----------------------
% 3.27/1.56  Preprocessing        : 0.32
% 3.27/1.56  Parsing              : 0.16
% 3.27/1.56  CNF conversion       : 0.02
% 3.27/1.56  Main loop            : 0.46
% 3.27/1.56  Inferencing          : 0.16
% 3.27/1.56  Reduction            : 0.14
% 3.27/1.56  Demodulation         : 0.10
% 3.27/1.56  BG Simplification    : 0.03
% 3.27/1.56  Subsumption          : 0.10
% 3.27/1.56  Abstraction          : 0.03
% 3.27/1.56  MUC search           : 0.00
% 3.27/1.56  Cooper               : 0.00
% 3.27/1.56  Total                : 0.81
% 3.27/1.56  Index Insertion      : 0.00
% 3.27/1.56  Index Deletion       : 0.00
% 3.27/1.56  Index Matching       : 0.00
% 3.27/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
