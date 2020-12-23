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
% DateTime   : Thu Dec  3 09:55:29 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 148 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :   88 ( 250 expanded)
%              Number of equality atoms :   47 ( 112 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_34,plain,(
    ! [A_19] : k2_subset_1(A_19) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_47,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_44])).

tff(c_26,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_7),A_5)
      | r2_hidden('#skF_2'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_732,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r2_hidden('#skF_1'(A_90,B_91,C_92),B_91)
      | r2_hidden('#skF_2'(A_90,B_91,C_92),C_92)
      | k4_xboole_0(A_90,B_91) = C_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_745,plain,(
    ! [A_5,C_7] :
      ( r2_hidden('#skF_2'(A_5,A_5,C_7),C_7)
      | k4_xboole_0(A_5,A_5) = C_7 ) ),
    inference(resolution,[status(thm)],[c_22,c_732])).

tff(c_749,plain,(
    ! [A_93,C_94] :
      ( r2_hidden('#skF_2'(A_93,A_93,C_94),C_94)
      | k4_xboole_0(A_93,A_93) = C_94 ) ),
    inference(resolution,[status(thm)],[c_22,c_732])).

tff(c_73,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [A_33] : k2_xboole_0(k1_xboole_0,A_33) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_26])).

tff(c_224,plain,(
    ! [A_48,B_49] : k2_xboole_0(A_48,k4_xboole_0(B_49,A_48)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_231,plain,(
    ! [B_49] : k4_xboole_0(B_49,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_89])).

tff(c_247,plain,(
    ! [B_50] : k4_xboole_0(B_50,k1_xboole_0) = B_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_231])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_262,plain,(
    ! [D_10,B_50] :
      ( ~ r2_hidden(D_10,k1_xboole_0)
      | ~ r2_hidden(D_10,B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_8])).

tff(c_774,plain,(
    ! [A_95,B_96] :
      ( ~ r2_hidden('#skF_2'(A_95,A_95,k1_xboole_0),B_96)
      | k4_xboole_0(A_95,A_95) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_749,c_262])).

tff(c_797,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_745,c_774])).

tff(c_896,plain,(
    ! [A_101,C_102] :
      ( r2_hidden('#skF_2'(A_101,A_101,C_102),C_102)
      | k1_xboole_0 = C_102 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_745])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( r2_hidden(D_10,A_5)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_925,plain,(
    ! [A_101,A_5,B_6] :
      ( r2_hidden('#skF_2'(A_101,A_101,k4_xboole_0(A_5,B_6)),A_5)
      | k4_xboole_0(A_5,B_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_896,c_10])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_403,plain,(
    ! [A_60,B_61] :
      ( k3_subset_1(A_60,k3_subset_1(A_60,B_61)) = B_61
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_409,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_403])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k3_subset_1(A_22,B_23),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_464,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k3_subset_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_526,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,k3_subset_1(A_72,B_73)) = k3_subset_1(A_72,k3_subset_1(A_72,B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(resolution,[status(thm)],[c_38,c_464])).

tff(c_530,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_526])).

tff(c_533,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_530])).

tff(c_543,plain,(
    ! [D_10] :
      ( r2_hidden(D_10,'#skF_3')
      | ~ r2_hidden(D_10,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_10])).

tff(c_1877,plain,(
    ! [A_150,A_151,B_152] :
      ( ~ r2_hidden('#skF_2'(A_150,A_150,k4_xboole_0(A_151,B_152)),B_152)
      | k4_xboole_0(A_151,B_152) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_896,c_8])).

tff(c_2026,plain,(
    ! [A_160,A_161] :
      ( k4_xboole_0(A_160,'#skF_3') = k1_xboole_0
      | ~ r2_hidden('#skF_2'(A_161,A_161,k4_xboole_0(A_160,'#skF_3')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_543,c_1877])).

tff(c_2041,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_925,c_2026])).

tff(c_28,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2059,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2041,c_28])).

tff(c_2074,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2,c_2059])).

tff(c_472,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_464])).

tff(c_476,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_28])).

tff(c_2081,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2074,c_476])).

tff(c_560,plain,(
    ! [A_75,B_76,C_77] :
      ( k4_subset_1(A_75,B_76,C_77) = k2_xboole_0(B_76,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_75))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2559,plain,(
    ! [A_194,B_195,B_196] :
      ( k4_subset_1(A_194,B_195,k3_subset_1(A_194,B_196)) = k2_xboole_0(B_195,k3_subset_1(A_194,B_196))
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_194))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(A_194)) ) ),
    inference(resolution,[status(thm)],[c_38,c_560])).

tff(c_2716,plain,(
    ! [B_202] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_202)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_202))
      | ~ m1_subset_1(B_202,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_2559])).

tff(c_2723,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_2716])).

tff(c_2726,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2081,c_2723])).

tff(c_2728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_2726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.10/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.71  
% 4.10/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.71  %$ r2_hidden > m1_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 4.10/1.71  
% 4.10/1.71  %Foreground sorts:
% 4.10/1.71  
% 4.10/1.71  
% 4.10/1.71  %Background operators:
% 4.10/1.71  
% 4.10/1.71  
% 4.10/1.71  %Foreground operators:
% 4.10/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.10/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.10/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.10/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.10/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.10/1.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.10/1.71  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.10/1.71  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.10/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.10/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.10/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.10/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.10/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.10/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.10/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.10/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.10/1.71  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.10/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.10/1.71  
% 4.10/1.72  tff(f_51, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.10/1.72  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 4.10/1.72  tff(f_43, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.10/1.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.10/1.72  tff(f_39, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.10/1.72  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.10/1.72  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.10/1.72  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.10/1.72  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.10/1.72  tff(f_69, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.10/1.72  tff(c_34, plain, (![A_19]: (k2_subset_1(A_19)=A_19)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.10/1.72  tff(c_44, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.10/1.72  tff(c_47, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_44])).
% 4.10/1.72  tff(c_26, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.10/1.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.10/1.72  tff(c_22, plain, (![A_5, B_6, C_7]: (r2_hidden('#skF_1'(A_5, B_6, C_7), A_5) | r2_hidden('#skF_2'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.10/1.72  tff(c_732, plain, (![A_90, B_91, C_92]: (~r2_hidden('#skF_1'(A_90, B_91, C_92), B_91) | r2_hidden('#skF_2'(A_90, B_91, C_92), C_92) | k4_xboole_0(A_90, B_91)=C_92)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.10/1.72  tff(c_745, plain, (![A_5, C_7]: (r2_hidden('#skF_2'(A_5, A_5, C_7), C_7) | k4_xboole_0(A_5, A_5)=C_7)), inference(resolution, [status(thm)], [c_22, c_732])).
% 4.10/1.72  tff(c_749, plain, (![A_93, C_94]: (r2_hidden('#skF_2'(A_93, A_93, C_94), C_94) | k4_xboole_0(A_93, A_93)=C_94)), inference(resolution, [status(thm)], [c_22, c_732])).
% 4.10/1.72  tff(c_73, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.10/1.72  tff(c_89, plain, (![A_33]: (k2_xboole_0(k1_xboole_0, A_33)=A_33)), inference(superposition, [status(thm), theory('equality')], [c_73, c_26])).
% 4.10/1.72  tff(c_224, plain, (![A_48, B_49]: (k2_xboole_0(A_48, k4_xboole_0(B_49, A_48))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.10/1.72  tff(c_231, plain, (![B_49]: (k4_xboole_0(B_49, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_49))), inference(superposition, [status(thm), theory('equality')], [c_224, c_89])).
% 4.10/1.72  tff(c_247, plain, (![B_50]: (k4_xboole_0(B_50, k1_xboole_0)=B_50)), inference(demodulation, [status(thm), theory('equality')], [c_89, c_231])).
% 4.10/1.72  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.10/1.72  tff(c_262, plain, (![D_10, B_50]: (~r2_hidden(D_10, k1_xboole_0) | ~r2_hidden(D_10, B_50))), inference(superposition, [status(thm), theory('equality')], [c_247, c_8])).
% 4.10/1.72  tff(c_774, plain, (![A_95, B_96]: (~r2_hidden('#skF_2'(A_95, A_95, k1_xboole_0), B_96) | k4_xboole_0(A_95, A_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_749, c_262])).
% 4.10/1.72  tff(c_797, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_745, c_774])).
% 4.10/1.72  tff(c_896, plain, (![A_101, C_102]: (r2_hidden('#skF_2'(A_101, A_101, C_102), C_102) | k1_xboole_0=C_102)), inference(demodulation, [status(thm), theory('equality')], [c_797, c_745])).
% 4.10/1.72  tff(c_10, plain, (![D_10, A_5, B_6]: (r2_hidden(D_10, A_5) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.10/1.72  tff(c_925, plain, (![A_101, A_5, B_6]: (r2_hidden('#skF_2'(A_101, A_101, k4_xboole_0(A_5, B_6)), A_5) | k4_xboole_0(A_5, B_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_896, c_10])).
% 4.10/1.72  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.10/1.72  tff(c_403, plain, (![A_60, B_61]: (k3_subset_1(A_60, k3_subset_1(A_60, B_61))=B_61 | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.10/1.72  tff(c_409, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_46, c_403])).
% 4.10/1.72  tff(c_38, plain, (![A_22, B_23]: (m1_subset_1(k3_subset_1(A_22, B_23), k1_zfmisc_1(A_22)) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.10/1.72  tff(c_464, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k3_subset_1(A_64, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.10/1.72  tff(c_526, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k3_subset_1(A_72, B_73))=k3_subset_1(A_72, k3_subset_1(A_72, B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(resolution, [status(thm)], [c_38, c_464])).
% 4.10/1.72  tff(c_530, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_526])).
% 4.10/1.72  tff(c_533, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_409, c_530])).
% 4.10/1.72  tff(c_543, plain, (![D_10]: (r2_hidden(D_10, '#skF_3') | ~r2_hidden(D_10, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_533, c_10])).
% 4.10/1.72  tff(c_1877, plain, (![A_150, A_151, B_152]: (~r2_hidden('#skF_2'(A_150, A_150, k4_xboole_0(A_151, B_152)), B_152) | k4_xboole_0(A_151, B_152)=k1_xboole_0)), inference(resolution, [status(thm)], [c_896, c_8])).
% 4.10/1.72  tff(c_2026, plain, (![A_160, A_161]: (k4_xboole_0(A_160, '#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_2'(A_161, A_161, k4_xboole_0(A_160, '#skF_3')), '#skF_4'))), inference(resolution, [status(thm)], [c_543, c_1877])).
% 4.10/1.72  tff(c_2041, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_925, c_2026])).
% 4.10/1.72  tff(c_28, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.10/1.72  tff(c_2059, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2041, c_28])).
% 4.10/1.72  tff(c_2074, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2, c_2059])).
% 4.10/1.72  tff(c_472, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_464])).
% 4.10/1.72  tff(c_476, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_472, c_28])).
% 4.10/1.72  tff(c_2081, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2074, c_476])).
% 4.10/1.72  tff(c_560, plain, (![A_75, B_76, C_77]: (k4_subset_1(A_75, B_76, C_77)=k2_xboole_0(B_76, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(A_75)) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.10/1.72  tff(c_2559, plain, (![A_194, B_195, B_196]: (k4_subset_1(A_194, B_195, k3_subset_1(A_194, B_196))=k2_xboole_0(B_195, k3_subset_1(A_194, B_196)) | ~m1_subset_1(B_195, k1_zfmisc_1(A_194)) | ~m1_subset_1(B_196, k1_zfmisc_1(A_194)))), inference(resolution, [status(thm)], [c_38, c_560])).
% 4.10/1.72  tff(c_2716, plain, (![B_202]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_202))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_202)) | ~m1_subset_1(B_202, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_46, c_2559])).
% 4.10/1.72  tff(c_2723, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_2716])).
% 4.10/1.72  tff(c_2726, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2081, c_2723])).
% 4.10/1.72  tff(c_2728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_2726])).
% 4.10/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.10/1.72  
% 4.10/1.72  Inference rules
% 4.10/1.72  ----------------------
% 4.10/1.72  #Ref     : 0
% 4.10/1.72  #Sup     : 588
% 4.10/1.72  #Fact    : 0
% 4.10/1.72  #Define  : 0
% 4.10/1.72  #Split   : 3
% 4.10/1.72  #Chain   : 0
% 4.10/1.72  #Close   : 0
% 4.10/1.72  
% 4.10/1.72  Ordering : KBO
% 4.10/1.72  
% 4.10/1.72  Simplification rules
% 4.10/1.72  ----------------------
% 4.10/1.72  #Subsume      : 56
% 4.10/1.72  #Demod        : 395
% 4.10/1.72  #Tautology    : 365
% 4.10/1.72  #SimpNegUnit  : 20
% 4.10/1.72  #BackRed      : 57
% 4.10/1.72  
% 4.10/1.72  #Partial instantiations: 0
% 4.10/1.72  #Strategies tried      : 1
% 4.10/1.72  
% 4.10/1.72  Timing (in seconds)
% 4.10/1.72  ----------------------
% 4.10/1.73  Preprocessing        : 0.32
% 4.10/1.73  Parsing              : 0.17
% 4.10/1.73  CNF conversion       : 0.02
% 4.10/1.73  Main loop            : 0.65
% 4.10/1.73  Inferencing          : 0.23
% 4.10/1.73  Reduction            : 0.23
% 4.10/1.73  Demodulation         : 0.17
% 4.10/1.73  BG Simplification    : 0.03
% 4.10/1.73  Subsumption          : 0.12
% 4.10/1.73  Abstraction          : 0.03
% 4.10/1.73  MUC search           : 0.00
% 4.10/1.73  Cooper               : 0.00
% 4.10/1.73  Total                : 1.00
% 4.10/1.73  Index Insertion      : 0.00
% 4.10/1.73  Index Deletion       : 0.00
% 4.10/1.73  Index Matching       : 0.00
% 4.10/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
