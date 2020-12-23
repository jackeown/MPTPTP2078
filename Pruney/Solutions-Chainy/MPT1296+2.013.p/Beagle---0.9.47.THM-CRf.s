%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:42 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 126 expanded)
%              Number of leaves         :   24 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 223 expanded)
%              Number of equality atoms :   35 ( 109 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_52,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_34,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) != k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [A_28,B_29] : ~ r2_hidden(A_28,k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_67,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_61])).

tff(c_92,plain,(
    ! [A_37,B_38] :
      ( k7_setfam_1(A_37,k7_setfam_1(A_37,B_38)) = B_38
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(A_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_99,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_92])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k7_setfam_1(A_20,B_21),k1_zfmisc_1(k1_zfmisc_1(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_115,plain,(
    ! [A_41,B_42] :
      ( k6_setfam_1(A_41,k7_setfam_1(A_41,B_42)) = k3_subset_1(A_41,k5_setfam_1(A_41,B_42))
      | k1_xboole_0 = B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_319,plain,(
    ! [A_65,B_66] :
      ( k6_setfam_1(A_65,k7_setfam_1(A_65,k7_setfam_1(A_65,B_66))) = k3_subset_1(A_65,k5_setfam_1(A_65,k7_setfam_1(A_65,B_66)))
      | k7_setfam_1(A_65,B_66) = k1_xboole_0
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(resolution,[status(thm)],[c_28,c_115])).

tff(c_329,plain,
    ( k6_setfam_1('#skF_2',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_319])).

tff(c_334,plain,
    ( k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_329])).

tff(c_335,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_334])).

tff(c_351,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_28])).

tff(c_361,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_351])).

tff(c_337,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_99])).

tff(c_488,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden('#skF_1'(A_72,B_73,C_74),C_74)
      | r2_hidden(k3_subset_1(A_72,'#skF_1'(A_72,B_73,C_74)),B_73)
      | k7_setfam_1(A_72,B_73) = C_74
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k1_zfmisc_1(A_72)))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k1_zfmisc_1(A_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_542,plain,(
    ! [A_80,C_81] :
      ( r2_hidden('#skF_1'(A_80,k1_xboole_0,C_81),C_81)
      | k7_setfam_1(A_80,k1_xboole_0) = C_81
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k1_zfmisc_1(A_80)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_80))) ) ),
    inference(resolution,[status(thm)],[c_488,c_67])).

tff(c_544,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_361,c_542])).

tff(c_557,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_337,c_544])).

tff(c_559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_67,c_557])).

tff(c_560,plain,(
    k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_334])).

tff(c_88,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k5_setfam_1(A_35,B_36),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_subset_1(A_5,k3_subset_1(A_5,B_6)) = B_6
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_144,plain,(
    ! [A_45,B_46] :
      ( k3_subset_1(A_45,k3_subset_1(A_45,k5_setfam_1(A_45,B_46))) = k5_setfam_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(resolution,[status(thm)],[c_88,c_10])).

tff(c_152,plain,(
    ! [A_20,B_21] :
      ( k3_subset_1(A_20,k3_subset_1(A_20,k5_setfam_1(A_20,k7_setfam_1(A_20,B_21)))) = k5_setfam_1(A_20,k7_setfam_1(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(resolution,[status(thm)],[c_28,c_144])).

tff(c_579,plain,
    ( k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_152])).

tff(c_583,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_579])).

tff(c_585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_583])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.38  
% 2.71/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.38  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.71/1.38  
% 2.71/1.38  %Foreground sorts:
% 2.71/1.38  
% 2.71/1.38  
% 2.71/1.38  %Background operators:
% 2.71/1.38  
% 2.71/1.38  
% 2.71/1.38  %Foreground operators:
% 2.71/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.71/1.38  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.71/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.71/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.71/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.71/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.71/1.38  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.38  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.71/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.71/1.38  
% 2.71/1.39  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 2.71/1.39  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.71/1.39  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.71/1.39  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.71/1.39  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.71/1.39  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 2.71/1.39  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.71/1.39  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.71/1.39  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.71/1.39  tff(c_34, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))!=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.71/1.39  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.71/1.39  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.71/1.39  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.71/1.39  tff(c_61, plain, (![A_28, B_29]: (~r2_hidden(A_28, k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.71/1.39  tff(c_67, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_61])).
% 2.71/1.39  tff(c_92, plain, (![A_37, B_38]: (k7_setfam_1(A_37, k7_setfam_1(A_37, B_38))=B_38 | ~m1_subset_1(B_38, k1_zfmisc_1(k1_zfmisc_1(A_37))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.71/1.39  tff(c_99, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_38, c_92])).
% 2.71/1.39  tff(c_28, plain, (![A_20, B_21]: (m1_subset_1(k7_setfam_1(A_20, B_21), k1_zfmisc_1(k1_zfmisc_1(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.71/1.39  tff(c_115, plain, (![A_41, B_42]: (k6_setfam_1(A_41, k7_setfam_1(A_41, B_42))=k3_subset_1(A_41, k5_setfam_1(A_41, B_42)) | k1_xboole_0=B_42 | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_41))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.71/1.39  tff(c_319, plain, (![A_65, B_66]: (k6_setfam_1(A_65, k7_setfam_1(A_65, k7_setfam_1(A_65, B_66)))=k3_subset_1(A_65, k5_setfam_1(A_65, k7_setfam_1(A_65, B_66))) | k7_setfam_1(A_65, B_66)=k1_xboole_0 | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(resolution, [status(thm)], [c_28, c_115])).
% 2.71/1.39  tff(c_329, plain, (k6_setfam_1('#skF_2', k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_319])).
% 2.71/1.39  tff(c_334, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_99, c_329])).
% 2.71/1.39  tff(c_335, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_334])).
% 2.71/1.39  tff(c_351, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_335, c_28])).
% 2.71/1.39  tff(c_361, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_351])).
% 2.71/1.39  tff(c_337, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_335, c_99])).
% 2.71/1.39  tff(c_488, plain, (![A_72, B_73, C_74]: (r2_hidden('#skF_1'(A_72, B_73, C_74), C_74) | r2_hidden(k3_subset_1(A_72, '#skF_1'(A_72, B_73, C_74)), B_73) | k7_setfam_1(A_72, B_73)=C_74 | ~m1_subset_1(C_74, k1_zfmisc_1(k1_zfmisc_1(A_72))) | ~m1_subset_1(B_73, k1_zfmisc_1(k1_zfmisc_1(A_72))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.71/1.39  tff(c_542, plain, (![A_80, C_81]: (r2_hidden('#skF_1'(A_80, k1_xboole_0, C_81), C_81) | k7_setfam_1(A_80, k1_xboole_0)=C_81 | ~m1_subset_1(C_81, k1_zfmisc_1(k1_zfmisc_1(A_80))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_80))))), inference(resolution, [status(thm)], [c_488, c_67])).
% 2.71/1.39  tff(c_544, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_361, c_542])).
% 2.71/1.39  tff(c_557, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_361, c_337, c_544])).
% 2.71/1.39  tff(c_559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_67, c_557])).
% 2.71/1.39  tff(c_560, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_334])).
% 2.71/1.39  tff(c_88, plain, (![A_35, B_36]: (m1_subset_1(k5_setfam_1(A_35, B_36), k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(A_35))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.71/1.39  tff(c_10, plain, (![A_5, B_6]: (k3_subset_1(A_5, k3_subset_1(A_5, B_6))=B_6 | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.71/1.39  tff(c_144, plain, (![A_45, B_46]: (k3_subset_1(A_45, k3_subset_1(A_45, k5_setfam_1(A_45, B_46)))=k5_setfam_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(resolution, [status(thm)], [c_88, c_10])).
% 2.71/1.39  tff(c_152, plain, (![A_20, B_21]: (k3_subset_1(A_20, k3_subset_1(A_20, k5_setfam_1(A_20, k7_setfam_1(A_20, B_21))))=k5_setfam_1(A_20, k7_setfam_1(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(resolution, [status(thm)], [c_28, c_144])).
% 2.71/1.39  tff(c_579, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_560, c_152])).
% 2.71/1.39  tff(c_583, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_579])).
% 2.71/1.39  tff(c_585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_583])).
% 2.71/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.39  
% 2.71/1.39  Inference rules
% 2.71/1.39  ----------------------
% 2.71/1.39  #Ref     : 0
% 2.71/1.39  #Sup     : 146
% 2.71/1.39  #Fact    : 0
% 2.71/1.39  #Define  : 0
% 2.71/1.39  #Split   : 2
% 2.71/1.39  #Chain   : 0
% 2.71/1.39  #Close   : 0
% 2.71/1.39  
% 2.71/1.39  Ordering : KBO
% 2.71/1.39  
% 2.71/1.39  Simplification rules
% 2.71/1.39  ----------------------
% 2.71/1.39  #Subsume      : 7
% 2.71/1.39  #Demod        : 60
% 2.71/1.39  #Tautology    : 67
% 2.71/1.39  #SimpNegUnit  : 6
% 2.71/1.39  #BackRed      : 4
% 2.71/1.39  
% 2.71/1.39  #Partial instantiations: 0
% 2.71/1.39  #Strategies tried      : 1
% 2.71/1.39  
% 2.71/1.39  Timing (in seconds)
% 2.71/1.39  ----------------------
% 2.71/1.39  Preprocessing        : 0.30
% 2.71/1.39  Parsing              : 0.16
% 2.71/1.39  CNF conversion       : 0.02
% 2.71/1.39  Main loop            : 0.32
% 2.71/1.39  Inferencing          : 0.12
% 2.71/1.39  Reduction            : 0.09
% 2.71/1.39  Demodulation         : 0.06
% 2.71/1.40  BG Simplification    : 0.02
% 2.71/1.40  Subsumption          : 0.07
% 2.71/1.40  Abstraction          : 0.02
% 2.71/1.40  MUC search           : 0.00
% 2.71/1.40  Cooper               : 0.00
% 2.71/1.40  Total                : 0.66
% 2.71/1.40  Index Insertion      : 0.00
% 2.71/1.40  Index Deletion       : 0.00
% 2.71/1.40  Index Matching       : 0.00
% 2.71/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
