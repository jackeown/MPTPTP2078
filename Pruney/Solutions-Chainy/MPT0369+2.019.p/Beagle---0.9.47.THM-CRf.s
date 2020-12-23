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
% DateTime   : Thu Dec  3 09:56:53 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 150 expanded)
%              Number of leaves         :   26 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 316 expanded)
%              Number of equality atoms :   25 (  52 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_606,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_625,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_606])).

tff(c_635,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_625])).

tff(c_1739,plain,(
    ! [A_156,B_157,C_158] :
      ( r2_hidden('#skF_2'(A_156,B_157,C_158),A_156)
      | r2_hidden('#skF_3'(A_156,B_157,C_158),C_158)
      | k4_xboole_0(A_156,B_157) = C_158 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6,C_7),B_6)
      | r2_hidden('#skF_3'(A_5,B_6,C_7),C_7)
      | k4_xboole_0(A_5,B_6) = C_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1746,plain,(
    ! [A_156,C_158] :
      ( r2_hidden('#skF_3'(A_156,A_156,C_158),C_158)
      | k4_xboole_0(A_156,A_156) = C_158 ) ),
    inference(resolution,[status(thm)],[c_1739,c_20])).

tff(c_1845,plain,(
    ! [A_159,C_160] :
      ( r2_hidden('#skF_3'(A_159,A_159,C_160),C_160)
      | k1_xboole_0 = C_160 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_1746])).

tff(c_48,plain,(
    m1_subset_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_92,plain,(
    ! [B_32,A_33] :
      ( v1_xboole_0(B_32)
      | ~ m1_subset_1(B_32,A_33)
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_100,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_92])).

tff(c_101,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( r2_hidden(B_19,A_18)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_380,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k3_subset_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_394,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_380])).

tff(c_485,plain,(
    ! [D_69,A_70,B_71] :
      ( r2_hidden(D_69,k4_xboole_0(A_70,B_71))
      | r2_hidden(D_69,B_71)
      | ~ r2_hidden(D_69,A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_549,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k3_subset_1('#skF_4','#skF_5'))
      | r2_hidden(D_72,'#skF_5')
      | ~ r2_hidden(D_72,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_485])).

tff(c_44,plain,(
    ~ r2_hidden('#skF_6',k3_subset_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_565,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_549,c_44])).

tff(c_578,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_565])).

tff(c_582,plain,
    ( ~ m1_subset_1('#skF_6','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_578])).

tff(c_585,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_582])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_585])).

tff(c_589,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_588,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_38,plain,(
    ! [B_19,A_18] :
      ( m1_subset_1(B_19,A_18)
      | ~ v1_xboole_0(B_19)
      | ~ v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_778,plain,(
    ! [B_90,A_91] :
      ( r2_hidden(B_90,A_91)
      | ~ m1_subset_1(B_90,A_91)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_797,plain,
    ( ~ m1_subset_1('#skF_6',k3_subset_1('#skF_4','#skF_5'))
    | v1_xboole_0(k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_778,c_44])).

tff(c_851,plain,(
    ~ m1_subset_1('#skF_6',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_797])).

tff(c_854,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_851])).

tff(c_857,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_854])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_882,plain,(
    ! [A_101,B_102] :
      ( k4_xboole_0(A_101,B_102) = k3_subset_1(A_101,B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_896,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_882])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( r2_hidden(D_10,A_5)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_931,plain,(
    ! [D_106] :
      ( r2_hidden(D_106,'#skF_4')
      | ~ r2_hidden(D_106,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_10])).

tff(c_939,plain,
    ( r2_hidden('#skF_1'(k3_subset_1('#skF_4','#skF_5')),'#skF_4')
    | v1_xboole_0(k3_subset_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_4,c_931])).

tff(c_945,plain,(
    r2_hidden('#skF_1'(k3_subset_1('#skF_4','#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_857,c_939])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_951,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_945,c_2])).

tff(c_957,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_951])).

tff(c_958,plain,(
    v1_xboole_0(k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_978,plain,(
    ! [A_109,B_110] :
      ( k4_xboole_0(A_109,B_110) = k3_subset_1(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_992,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_978])).

tff(c_30,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1002,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_4','#skF_5')) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_30])).

tff(c_816,plain,(
    ! [D_94,A_95,B_96] :
      ( r2_hidden(D_94,A_95)
      | ~ r2_hidden(D_94,k4_xboole_0(A_95,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1201,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_125,B_126)),A_125)
      | v1_xboole_0(k4_xboole_0(A_125,B_126)) ) ),
    inference(resolution,[status(thm)],[c_4,c_816])).

tff(c_1281,plain,(
    ! [A_127,B_128] :
      ( ~ v1_xboole_0(A_127)
      | v1_xboole_0(k4_xboole_0(A_127,B_128)) ) ),
    inference(resolution,[status(thm)],[c_1201,c_2])).

tff(c_1287,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_1281])).

tff(c_1304,plain,(
    v1_xboole_0(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_1287])).

tff(c_1153,plain,(
    ! [D_122,A_123,B_124] :
      ( r2_hidden(D_122,k4_xboole_0(A_123,B_124))
      | r2_hidden(D_122,B_124)
      | ~ r2_hidden(D_122,A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1341,plain,(
    ! [A_132,B_133,D_134] :
      ( ~ v1_xboole_0(k4_xboole_0(A_132,B_133))
      | r2_hidden(D_134,B_133)
      | ~ r2_hidden(D_134,A_132) ) ),
    inference(resolution,[status(thm)],[c_1153,c_2])).

tff(c_1347,plain,(
    ! [D_134] :
      ( ~ v1_xboole_0(k3_xboole_0('#skF_4','#skF_5'))
      | r2_hidden(D_134,k3_subset_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_134,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_1341])).

tff(c_1427,plain,(
    ! [D_140] :
      ( r2_hidden(D_140,k3_subset_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_140,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1304,c_1347])).

tff(c_1450,plain,(
    ! [D_140] :
      ( ~ v1_xboole_0(k3_subset_1('#skF_4','#skF_5'))
      | ~ r2_hidden(D_140,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1427,c_2])).

tff(c_1460,plain,(
    ! [D_140] : ~ r2_hidden(D_140,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_1450])).

tff(c_1857,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1845,c_1460])).

tff(c_1891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1857])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.52  
% 3.10/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.52  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.10/1.52  
% 3.10/1.52  %Foreground sorts:
% 3.10/1.52  
% 3.10/1.52  
% 3.10/1.52  %Background operators:
% 3.10/1.52  
% 3.10/1.52  
% 3.10/1.52  %Foreground operators:
% 3.10/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.10/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.10/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.10/1.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.10/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.10/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.10/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.10/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.52  
% 3.35/1.54  tff(f_83, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 3.35/1.54  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.35/1.54  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.35/1.54  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.35/1.54  tff(f_41, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.35/1.54  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.35/1.54  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.35/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.35/1.54  tff(c_52, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.35/1.54  tff(c_26, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.35/1.54  tff(c_28, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.35/1.54  tff(c_606, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.35/1.54  tff(c_625, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_606])).
% 3.35/1.54  tff(c_635, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_625])).
% 3.35/1.54  tff(c_1739, plain, (![A_156, B_157, C_158]: (r2_hidden('#skF_2'(A_156, B_157, C_158), A_156) | r2_hidden('#skF_3'(A_156, B_157, C_158), C_158) | k4_xboole_0(A_156, B_157)=C_158)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.54  tff(c_20, plain, (![A_5, B_6, C_7]: (~r2_hidden('#skF_2'(A_5, B_6, C_7), B_6) | r2_hidden('#skF_3'(A_5, B_6, C_7), C_7) | k4_xboole_0(A_5, B_6)=C_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.54  tff(c_1746, plain, (![A_156, C_158]: (r2_hidden('#skF_3'(A_156, A_156, C_158), C_158) | k4_xboole_0(A_156, A_156)=C_158)), inference(resolution, [status(thm)], [c_1739, c_20])).
% 3.35/1.54  tff(c_1845, plain, (![A_159, C_160]: (r2_hidden('#skF_3'(A_159, A_159, C_160), C_160) | k1_xboole_0=C_160)), inference(demodulation, [status(thm), theory('equality')], [c_635, c_1746])).
% 3.35/1.54  tff(c_48, plain, (m1_subset_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.35/1.54  tff(c_92, plain, (![B_32, A_33]: (v1_xboole_0(B_32) | ~m1_subset_1(B_32, A_33) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.35/1.54  tff(c_100, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_92])).
% 3.35/1.54  tff(c_101, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_100])).
% 3.35/1.54  tff(c_36, plain, (![B_19, A_18]: (r2_hidden(B_19, A_18) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.35/1.54  tff(c_46, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.35/1.54  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.35/1.54  tff(c_380, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k3_subset_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.35/1.54  tff(c_394, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_380])).
% 3.35/1.54  tff(c_485, plain, (![D_69, A_70, B_71]: (r2_hidden(D_69, k4_xboole_0(A_70, B_71)) | r2_hidden(D_69, B_71) | ~r2_hidden(D_69, A_70))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.54  tff(c_549, plain, (![D_72]: (r2_hidden(D_72, k3_subset_1('#skF_4', '#skF_5')) | r2_hidden(D_72, '#skF_5') | ~r2_hidden(D_72, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_394, c_485])).
% 3.35/1.54  tff(c_44, plain, (~r2_hidden('#skF_6', k3_subset_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.35/1.54  tff(c_565, plain, (r2_hidden('#skF_6', '#skF_5') | ~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_549, c_44])).
% 3.35/1.54  tff(c_578, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_565])).
% 3.35/1.54  tff(c_582, plain, (~m1_subset_1('#skF_6', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_578])).
% 3.35/1.54  tff(c_585, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_582])).
% 3.35/1.54  tff(c_587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_585])).
% 3.35/1.54  tff(c_589, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_100])).
% 3.35/1.54  tff(c_588, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_100])).
% 3.35/1.54  tff(c_38, plain, (![B_19, A_18]: (m1_subset_1(B_19, A_18) | ~v1_xboole_0(B_19) | ~v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.35/1.54  tff(c_778, plain, (![B_90, A_91]: (r2_hidden(B_90, A_91) | ~m1_subset_1(B_90, A_91) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.35/1.54  tff(c_797, plain, (~m1_subset_1('#skF_6', k3_subset_1('#skF_4', '#skF_5')) | v1_xboole_0(k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_778, c_44])).
% 3.35/1.54  tff(c_851, plain, (~m1_subset_1('#skF_6', k3_subset_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_797])).
% 3.35/1.54  tff(c_854, plain, (~v1_xboole_0('#skF_6') | ~v1_xboole_0(k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_851])).
% 3.35/1.54  tff(c_857, plain, (~v1_xboole_0(k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_854])).
% 3.35/1.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.35/1.54  tff(c_882, plain, (![A_101, B_102]: (k4_xboole_0(A_101, B_102)=k3_subset_1(A_101, B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.35/1.54  tff(c_896, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_882])).
% 3.35/1.54  tff(c_10, plain, (![D_10, A_5, B_6]: (r2_hidden(D_10, A_5) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.54  tff(c_931, plain, (![D_106]: (r2_hidden(D_106, '#skF_4') | ~r2_hidden(D_106, k3_subset_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_896, c_10])).
% 3.35/1.54  tff(c_939, plain, (r2_hidden('#skF_1'(k3_subset_1('#skF_4', '#skF_5')), '#skF_4') | v1_xboole_0(k3_subset_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_4, c_931])).
% 3.35/1.54  tff(c_945, plain, (r2_hidden('#skF_1'(k3_subset_1('#skF_4', '#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_857, c_939])).
% 3.35/1.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.35/1.54  tff(c_951, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_945, c_2])).
% 3.35/1.54  tff(c_957, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_589, c_951])).
% 3.35/1.54  tff(c_958, plain, (v1_xboole_0(k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_797])).
% 3.35/1.54  tff(c_978, plain, (![A_109, B_110]: (k4_xboole_0(A_109, B_110)=k3_subset_1(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_109)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.35/1.54  tff(c_992, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_978])).
% 3.35/1.54  tff(c_30, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.35/1.54  tff(c_1002, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_4', '#skF_5'))=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_992, c_30])).
% 3.35/1.54  tff(c_816, plain, (![D_94, A_95, B_96]: (r2_hidden(D_94, A_95) | ~r2_hidden(D_94, k4_xboole_0(A_95, B_96)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.54  tff(c_1201, plain, (![A_125, B_126]: (r2_hidden('#skF_1'(k4_xboole_0(A_125, B_126)), A_125) | v1_xboole_0(k4_xboole_0(A_125, B_126)))), inference(resolution, [status(thm)], [c_4, c_816])).
% 3.35/1.54  tff(c_1281, plain, (![A_127, B_128]: (~v1_xboole_0(A_127) | v1_xboole_0(k4_xboole_0(A_127, B_128)))), inference(resolution, [status(thm)], [c_1201, c_2])).
% 3.35/1.54  tff(c_1287, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_1281])).
% 3.35/1.54  tff(c_1304, plain, (v1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_589, c_1287])).
% 3.35/1.54  tff(c_1153, plain, (![D_122, A_123, B_124]: (r2_hidden(D_122, k4_xboole_0(A_123, B_124)) | r2_hidden(D_122, B_124) | ~r2_hidden(D_122, A_123))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.35/1.54  tff(c_1341, plain, (![A_132, B_133, D_134]: (~v1_xboole_0(k4_xboole_0(A_132, B_133)) | r2_hidden(D_134, B_133) | ~r2_hidden(D_134, A_132))), inference(resolution, [status(thm)], [c_1153, c_2])).
% 3.35/1.54  tff(c_1347, plain, (![D_134]: (~v1_xboole_0(k3_xboole_0('#skF_4', '#skF_5')) | r2_hidden(D_134, k3_subset_1('#skF_4', '#skF_5')) | ~r2_hidden(D_134, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_1341])).
% 3.35/1.54  tff(c_1427, plain, (![D_140]: (r2_hidden(D_140, k3_subset_1('#skF_4', '#skF_5')) | ~r2_hidden(D_140, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1304, c_1347])).
% 3.35/1.54  tff(c_1450, plain, (![D_140]: (~v1_xboole_0(k3_subset_1('#skF_4', '#skF_5')) | ~r2_hidden(D_140, '#skF_4'))), inference(resolution, [status(thm)], [c_1427, c_2])).
% 3.35/1.54  tff(c_1460, plain, (![D_140]: (~r2_hidden(D_140, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_958, c_1450])).
% 3.35/1.54  tff(c_1857, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1845, c_1460])).
% 3.35/1.54  tff(c_1891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1857])).
% 3.35/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.54  
% 3.35/1.54  Inference rules
% 3.35/1.54  ----------------------
% 3.35/1.54  #Ref     : 0
% 3.35/1.54  #Sup     : 411
% 3.35/1.54  #Fact    : 0
% 3.35/1.54  #Define  : 0
% 3.35/1.54  #Split   : 11
% 3.35/1.54  #Chain   : 0
% 3.35/1.54  #Close   : 0
% 3.35/1.54  
% 3.35/1.54  Ordering : KBO
% 3.35/1.54  
% 3.35/1.54  Simplification rules
% 3.35/1.54  ----------------------
% 3.35/1.54  #Subsume      : 53
% 3.35/1.54  #Demod        : 146
% 3.35/1.54  #Tautology    : 185
% 3.35/1.54  #SimpNegUnit  : 25
% 3.35/1.54  #BackRed      : 1
% 3.35/1.54  
% 3.35/1.54  #Partial instantiations: 0
% 3.35/1.54  #Strategies tried      : 1
% 3.35/1.54  
% 3.35/1.54  Timing (in seconds)
% 3.35/1.54  ----------------------
% 3.35/1.54  Preprocessing        : 0.30
% 3.35/1.54  Parsing              : 0.15
% 3.35/1.54  CNF conversion       : 0.02
% 3.35/1.54  Main loop            : 0.46
% 3.35/1.54  Inferencing          : 0.17
% 3.35/1.54  Reduction            : 0.14
% 3.35/1.54  Demodulation         : 0.10
% 3.35/1.54  BG Simplification    : 0.02
% 3.35/1.54  Subsumption          : 0.08
% 3.35/1.54  Abstraction          : 0.02
% 3.35/1.54  MUC search           : 0.00
% 3.35/1.54  Cooper               : 0.00
% 3.35/1.54  Total                : 0.79
% 3.35/1.54  Index Insertion      : 0.00
% 3.35/1.54  Index Deletion       : 0.00
% 3.35/1.54  Index Matching       : 0.00
% 3.35/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
