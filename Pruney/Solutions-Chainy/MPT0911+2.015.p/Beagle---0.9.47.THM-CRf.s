%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:03 EST 2020

% Result     : Theorem 23.02s
% Output     : CNFRefutation 23.02s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 347 expanded)
%              Number of leaves         :   43 ( 139 expanded)
%              Depth                    :   15
%              Number of atoms          :  201 (1068 expanded)
%              Number of equality atoms :  102 ( 577 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_89,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ v1_xboole_0(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_567,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( k7_mcart_1(A_186,B_187,C_188,D_189) = k2_mcart_1(D_189)
      | ~ m1_subset_1(D_189,k3_zfmisc_1(A_186,B_187,C_188))
      | k1_xboole_0 = C_188
      | k1_xboole_0 = B_187
      | k1_xboole_0 = A_186 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_591,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_567])).

tff(c_600,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_591])).

tff(c_54,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_601,plain,(
    k2_mcart_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_54])).

tff(c_24,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( m1_subset_1(k7_mcart_1(A_29,B_30,C_31,D_32),C_31)
      | ~ m1_subset_1(D_32,k3_zfmisc_1(A_29,B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_605,plain,
    ( m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5')
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_600,c_24])).

tff(c_609,plain,(
    m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_605])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [A_61,B_62,D_64] : k4_zfmisc_1(A_61,B_62,k1_xboole_0,D_64) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_32,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_2'(A_38),A_38)
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_217,plain,(
    ! [A_120,C_121,B_122] :
      ( r2_hidden(k2_mcart_1(A_120),C_121)
      | ~ r2_hidden(A_120,k2_zfmisc_1(B_122,C_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_296,plain,(
    ! [B_146,C_147] :
      ( r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_146,C_147))),C_147)
      | k2_zfmisc_1(B_146,C_147) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_217])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_340,plain,(
    ! [C_153,B_154] :
      ( ~ v1_xboole_0(C_153)
      | k2_zfmisc_1(B_154,C_153) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_296,c_2])).

tff(c_344,plain,(
    ! [B_155] : k2_zfmisc_1(B_155,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_340])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_383,plain,(
    ! [A_156,B_157] : k3_zfmisc_1(A_156,B_157,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_16])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19,D_20] : k2_zfmisc_1(k3_zfmisc_1(A_17,B_18,C_19),D_20) = k4_zfmisc_1(A_17,B_18,C_19,D_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_388,plain,(
    ! [A_156,B_157,D_20] : k4_zfmisc_1(A_156,B_157,k1_xboole_0,D_20) = k2_zfmisc_1(k1_xboole_0,D_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_18])).

tff(c_396,plain,(
    ! [D_20] : k2_zfmisc_1(k1_xboole_0,D_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_388])).

tff(c_166,plain,(
    ! [A_105,B_106,C_107] : k2_zfmisc_1(k2_zfmisc_1(A_105,B_106),C_107) = k3_zfmisc_1(A_105,B_106,C_107) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_174,plain,(
    ! [A_105,B_106,C_107] : v1_relat_1(k3_zfmisc_1(A_105,B_106,C_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_12])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_245,plain,(
    ! [A_127,B_128] :
      ( k4_tarski(k1_mcart_1(A_127),k2_mcart_1(A_127)) = A_127
      | ~ r2_hidden(A_127,B_128)
      | ~ v1_relat_1(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6346,plain,(
    ! [A_449,B_450] :
      ( k4_tarski(k1_mcart_1(A_449),k2_mcart_1(A_449)) = A_449
      | ~ v1_relat_1(B_450)
      | v1_xboole_0(B_450)
      | ~ m1_subset_1(A_449,B_450) ) ),
    inference(resolution,[status(thm)],[c_10,c_245])).

tff(c_6356,plain,
    ( k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_3','#skF_4','#skF_5'))
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_6346])).

tff(c_6363,plain,
    ( k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_6356])).

tff(c_6364,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6363])).

tff(c_119,plain,(
    ! [A_98] :
      ( r2_hidden('#skF_2'(A_98),A_98)
      | k1_xboole_0 = A_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_123,plain,(
    ! [A_98] :
      ( ~ v1_xboole_0(A_98)
      | k1_xboole_0 = A_98 ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_6398,plain,(
    k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6364,c_123])).

tff(c_6457,plain,(
    ! [D_20] : k4_zfmisc_1('#skF_3','#skF_4','#skF_5',D_20) = k2_zfmisc_1(k1_xboole_0,D_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_6398,c_18])).

tff(c_6490,plain,(
    ! [D_451] : k4_zfmisc_1('#skF_3','#skF_4','#skF_5',D_451) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_6457])).

tff(c_44,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k4_zfmisc_1(A_61,B_62,C_63,D_64) != k1_xboole_0
      | k1_xboole_0 = D_64
      | k1_xboole_0 = C_63
      | k1_xboole_0 = B_62
      | k1_xboole_0 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6530,plain,(
    ! [D_451] :
      ( k1_xboole_0 = D_451
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6490,c_44])).

tff(c_6573,plain,(
    ! [D_452] : k1_xboole_0 = D_452 ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_6530])).

tff(c_183,plain,(
    ! [A_108,B_109,C_110] : k4_tarski(k4_tarski(A_108,B_109),C_110) = k3_mcart_1(A_108,B_109,C_110) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_5,B_6] : ~ v1_xboole_0(k4_tarski(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_191,plain,(
    ! [A_108,B_109,C_110] : ~ v1_xboole_0(k3_mcart_1(A_108,B_109,C_110)) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_8])).

tff(c_6693,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6573,c_191])).

tff(c_6754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6693])).

tff(c_6755,plain,(
    k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6363])).

tff(c_22,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( m1_subset_1(k6_mcart_1(A_25,B_26,C_27,D_28),B_26)
      | ~ m1_subset_1(D_28,k3_zfmisc_1(A_25,B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_21,B_22,C_23,D_24] :
      ( m1_subset_1(k5_mcart_1(A_21,B_22,C_23,D_24),A_21)
      | ~ m1_subset_1(D_24,k3_zfmisc_1(A_21,B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_686,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( k5_mcart_1(A_194,B_195,C_196,D_197) = k1_mcart_1(k1_mcart_1(D_197))
      | ~ m1_subset_1(D_197,k3_zfmisc_1(A_194,B_195,C_196))
      | k1_xboole_0 = C_196
      | k1_xboole_0 = B_195
      | k1_xboole_0 = A_194 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_710,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_686])).

tff(c_719,plain,(
    k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_710])).

tff(c_741,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( k6_mcart_1(A_203,B_204,C_205,D_206) = k2_mcart_1(k1_mcart_1(D_206))
      | ~ m1_subset_1(D_206,k3_zfmisc_1(A_203,B_204,C_205))
      | k1_xboole_0 = C_205
      | k1_xboole_0 = B_204
      | k1_xboole_0 = A_203 ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_765,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_741])).

tff(c_774,plain,(
    k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_58,c_56,c_765])).

tff(c_6756,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6363])).

tff(c_202,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_hidden(k1_mcart_1(A_117),B_118)
      | ~ r2_hidden(A_117,k2_zfmisc_1(B_118,C_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4164,plain,(
    ! [A_388,A_389,B_390,C_391] :
      ( r2_hidden(k1_mcart_1(A_388),k2_zfmisc_1(A_389,B_390))
      | ~ r2_hidden(A_388,k3_zfmisc_1(A_389,B_390,C_391)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_202])).

tff(c_153987,plain,(
    ! [A_3662,A_3663,B_3664,C_3665] :
      ( r2_hidden(k1_mcart_1(A_3662),k2_zfmisc_1(A_3663,B_3664))
      | v1_xboole_0(k3_zfmisc_1(A_3663,B_3664,C_3665))
      | ~ m1_subset_1(A_3662,k3_zfmisc_1(A_3663,B_3664,C_3665)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4164])).

tff(c_154136,plain,
    ( r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_153987])).

tff(c_154150,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_6756,c_154136])).

tff(c_30,plain,(
    ! [A_36,B_37] :
      ( k4_tarski(k1_mcart_1(A_36),k2_mcart_1(A_36)) = A_36
      | ~ r2_hidden(A_36,B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_154156,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_7')),k2_mcart_1(k1_mcart_1('#skF_7'))) = k1_mcart_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_154150,c_30])).

tff(c_154168,plain,(
    k4_tarski(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')) = k1_mcart_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_719,c_774,c_154156])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k4_tarski(k4_tarski(A_11,B_12),C_13) = k3_mcart_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_155156,plain,(
    ! [C_3692] : k3_mcart_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),C_3692) = k4_tarski(k1_mcart_1('#skF_7'),C_3692) ),
    inference(superposition,[status(thm),theory(equality)],[c_154168,c_14])).

tff(c_62,plain,(
    ! [H_78,F_72,G_76] :
      ( H_78 = '#skF_6'
      | k3_mcart_1(F_72,G_76,H_78) != '#skF_7'
      | ~ m1_subset_1(H_78,'#skF_5')
      | ~ m1_subset_1(G_76,'#skF_4')
      | ~ m1_subset_1(F_72,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_155165,plain,(
    ! [C_3692] :
      ( C_3692 = '#skF_6'
      | k4_tarski(k1_mcart_1('#skF_7'),C_3692) != '#skF_7'
      | ~ m1_subset_1(C_3692,'#skF_5')
      | ~ m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4')
      | ~ m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155156,c_62])).

tff(c_156922,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_155165])).

tff(c_156925,plain,(
    ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_156922])).

tff(c_156929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_156925])).

tff(c_156930,plain,(
    ! [C_3692] :
      ( ~ m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4')
      | C_3692 = '#skF_6'
      | k4_tarski(k1_mcart_1('#skF_7'),C_3692) != '#skF_7'
      | ~ m1_subset_1(C_3692,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_155165])).

tff(c_156937,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_156930])).

tff(c_156940,plain,(
    ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_22,c_156937])).

tff(c_156944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_156940])).

tff(c_156952,plain,(
    ! [C_3704] :
      ( C_3704 = '#skF_6'
      | k4_tarski(k1_mcart_1('#skF_7'),C_3704) != '#skF_7'
      | ~ m1_subset_1(C_3704,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_156930])).

tff(c_156955,plain,
    ( k2_mcart_1('#skF_7') = '#skF_6'
    | ~ m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6755,c_156952])).

tff(c_156958,plain,(
    k2_mcart_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_156955])).

tff(c_156960,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_601,c_156958])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.02/14.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.02/14.56  
% 23.02/14.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.02/14.56  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 23.02/14.56  
% 23.02/14.56  %Foreground sorts:
% 23.02/14.56  
% 23.02/14.56  
% 23.02/14.56  %Background operators:
% 23.02/14.56  
% 23.02/14.56  
% 23.02/14.56  %Foreground operators:
% 23.02/14.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 23.02/14.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.02/14.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.02/14.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 23.02/14.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 23.02/14.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.02/14.56  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 23.02/14.56  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 23.02/14.56  tff('#skF_7', type, '#skF_7': $i).
% 23.02/14.56  tff('#skF_5', type, '#skF_5': $i).
% 23.02/14.56  tff('#skF_6', type, '#skF_6': $i).
% 23.02/14.56  tff('#skF_3', type, '#skF_3': $i).
% 23.02/14.56  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 23.02/14.56  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 23.02/14.56  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 23.02/14.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.02/14.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 23.02/14.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.02/14.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.02/14.56  tff('#skF_4', type, '#skF_4': $i).
% 23.02/14.56  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 23.02/14.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.02/14.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 23.02/14.56  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 23.02/14.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.02/14.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.02/14.56  
% 23.02/14.58  tff(f_148, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 23.02/14.58  tff(f_109, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 23.02/14.58  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 23.02/14.58  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 23.02/14.58  tff(f_124, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 23.02/14.58  tff(f_89, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 23.02/14.58  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 23.02/14.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 23.02/14.58  tff(f_47, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 23.02/14.58  tff(f_49, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 23.02/14.58  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 23.02/14.58  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 23.02/14.58  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 23.02/14.58  tff(f_45, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 23.02/14.58  tff(f_35, axiom, (![A, B]: ~v1_xboole_0(k4_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_zfmisc_1)).
% 23.02/14.58  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 23.02/14.58  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k5_mcart_1(A, B, C, D), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 23.02/14.58  tff(c_60, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_148])).
% 23.02/14.58  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_148])).
% 23.02/14.58  tff(c_56, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_148])).
% 23.02/14.58  tff(c_64, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 23.02/14.58  tff(c_567, plain, (![A_186, B_187, C_188, D_189]: (k7_mcart_1(A_186, B_187, C_188, D_189)=k2_mcart_1(D_189) | ~m1_subset_1(D_189, k3_zfmisc_1(A_186, B_187, C_188)) | k1_xboole_0=C_188 | k1_xboole_0=B_187 | k1_xboole_0=A_186)), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.02/14.58  tff(c_591, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_64, c_567])).
% 23.02/14.58  tff(c_600, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_591])).
% 23.02/14.58  tff(c_54, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_148])).
% 23.02/14.58  tff(c_601, plain, (k2_mcart_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_600, c_54])).
% 23.02/14.58  tff(c_24, plain, (![A_29, B_30, C_31, D_32]: (m1_subset_1(k7_mcart_1(A_29, B_30, C_31, D_32), C_31) | ~m1_subset_1(D_32, k3_zfmisc_1(A_29, B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 23.02/14.58  tff(c_605, plain, (m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5') | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_600, c_24])).
% 23.02/14.58  tff(c_609, plain, (m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_605])).
% 23.02/14.58  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 23.02/14.58  tff(c_48, plain, (![A_61, B_62, D_64]: (k4_zfmisc_1(A_61, B_62, k1_xboole_0, D_64)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_124])).
% 23.02/14.58  tff(c_32, plain, (![A_38]: (r2_hidden('#skF_2'(A_38), A_38) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.02/14.58  tff(c_217, plain, (![A_120, C_121, B_122]: (r2_hidden(k2_mcart_1(A_120), C_121) | ~r2_hidden(A_120, k2_zfmisc_1(B_122, C_121)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.02/14.58  tff(c_296, plain, (![B_146, C_147]: (r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_146, C_147))), C_147) | k2_zfmisc_1(B_146, C_147)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_217])).
% 23.02/14.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.02/14.58  tff(c_340, plain, (![C_153, B_154]: (~v1_xboole_0(C_153) | k2_zfmisc_1(B_154, C_153)=k1_xboole_0)), inference(resolution, [status(thm)], [c_296, c_2])).
% 23.02/14.58  tff(c_344, plain, (![B_155]: (k2_zfmisc_1(B_155, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_340])).
% 23.02/14.58  tff(c_16, plain, (![A_14, B_15, C_16]: (k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.02/14.58  tff(c_383, plain, (![A_156, B_157]: (k3_zfmisc_1(A_156, B_157, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_344, c_16])).
% 23.02/14.58  tff(c_18, plain, (![A_17, B_18, C_19, D_20]: (k2_zfmisc_1(k3_zfmisc_1(A_17, B_18, C_19), D_20)=k4_zfmisc_1(A_17, B_18, C_19, D_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 23.02/14.58  tff(c_388, plain, (![A_156, B_157, D_20]: (k4_zfmisc_1(A_156, B_157, k1_xboole_0, D_20)=k2_zfmisc_1(k1_xboole_0, D_20))), inference(superposition, [status(thm), theory('equality')], [c_383, c_18])).
% 23.02/14.58  tff(c_396, plain, (![D_20]: (k2_zfmisc_1(k1_xboole_0, D_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_388])).
% 23.02/14.58  tff(c_166, plain, (![A_105, B_106, C_107]: (k2_zfmisc_1(k2_zfmisc_1(A_105, B_106), C_107)=k3_zfmisc_1(A_105, B_106, C_107))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.02/14.58  tff(c_12, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.02/14.58  tff(c_174, plain, (![A_105, B_106, C_107]: (v1_relat_1(k3_zfmisc_1(A_105, B_106, C_107)))), inference(superposition, [status(thm), theory('equality')], [c_166, c_12])).
% 23.02/14.58  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.02/14.58  tff(c_245, plain, (![A_127, B_128]: (k4_tarski(k1_mcart_1(A_127), k2_mcart_1(A_127))=A_127 | ~r2_hidden(A_127, B_128) | ~v1_relat_1(B_128))), inference(cnfTransformation, [status(thm)], [f_73])).
% 23.02/14.58  tff(c_6346, plain, (![A_449, B_450]: (k4_tarski(k1_mcart_1(A_449), k2_mcart_1(A_449))=A_449 | ~v1_relat_1(B_450) | v1_xboole_0(B_450) | ~m1_subset_1(A_449, B_450))), inference(resolution, [status(thm)], [c_10, c_245])).
% 23.02/14.58  tff(c_6356, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~v1_relat_1(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_6346])).
% 23.02/14.58  tff(c_6363, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_6356])).
% 23.02/14.58  tff(c_6364, plain, (v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_6363])).
% 23.02/14.58  tff(c_119, plain, (![A_98]: (r2_hidden('#skF_2'(A_98), A_98) | k1_xboole_0=A_98)), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.02/14.58  tff(c_123, plain, (![A_98]: (~v1_xboole_0(A_98) | k1_xboole_0=A_98)), inference(resolution, [status(thm)], [c_119, c_2])).
% 23.02/14.58  tff(c_6398, plain, (k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_6364, c_123])).
% 23.02/14.58  tff(c_6457, plain, (![D_20]: (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', D_20)=k2_zfmisc_1(k1_xboole_0, D_20))), inference(superposition, [status(thm), theory('equality')], [c_6398, c_18])).
% 23.02/14.58  tff(c_6490, plain, (![D_451]: (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', D_451)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_396, c_6457])).
% 23.02/14.58  tff(c_44, plain, (![A_61, B_62, C_63, D_64]: (k4_zfmisc_1(A_61, B_62, C_63, D_64)!=k1_xboole_0 | k1_xboole_0=D_64 | k1_xboole_0=C_63 | k1_xboole_0=B_62 | k1_xboole_0=A_61)), inference(cnfTransformation, [status(thm)], [f_124])).
% 23.02/14.58  tff(c_6530, plain, (![D_451]: (k1_xboole_0=D_451 | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6490, c_44])).
% 23.02/14.58  tff(c_6573, plain, (![D_452]: (k1_xboole_0=D_452)), inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_6530])).
% 23.02/14.58  tff(c_183, plain, (![A_108, B_109, C_110]: (k4_tarski(k4_tarski(A_108, B_109), C_110)=k3_mcart_1(A_108, B_109, C_110))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.02/14.58  tff(c_8, plain, (![A_5, B_6]: (~v1_xboole_0(k4_tarski(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.02/14.58  tff(c_191, plain, (![A_108, B_109, C_110]: (~v1_xboole_0(k3_mcart_1(A_108, B_109, C_110)))), inference(superposition, [status(thm), theory('equality')], [c_183, c_8])).
% 23.02/14.58  tff(c_6693, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6573, c_191])).
% 23.02/14.58  tff(c_6754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6693])).
% 23.02/14.58  tff(c_6755, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(splitRight, [status(thm)], [c_6363])).
% 23.02/14.58  tff(c_22, plain, (![A_25, B_26, C_27, D_28]: (m1_subset_1(k6_mcart_1(A_25, B_26, C_27, D_28), B_26) | ~m1_subset_1(D_28, k3_zfmisc_1(A_25, B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 23.02/14.58  tff(c_20, plain, (![A_21, B_22, C_23, D_24]: (m1_subset_1(k5_mcart_1(A_21, B_22, C_23, D_24), A_21) | ~m1_subset_1(D_24, k3_zfmisc_1(A_21, B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.02/14.58  tff(c_686, plain, (![A_194, B_195, C_196, D_197]: (k5_mcart_1(A_194, B_195, C_196, D_197)=k1_mcart_1(k1_mcart_1(D_197)) | ~m1_subset_1(D_197, k3_zfmisc_1(A_194, B_195, C_196)) | k1_xboole_0=C_196 | k1_xboole_0=B_195 | k1_xboole_0=A_194)), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.02/14.58  tff(c_710, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_64, c_686])).
% 23.02/14.58  tff(c_719, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_710])).
% 23.02/14.58  tff(c_741, plain, (![A_203, B_204, C_205, D_206]: (k6_mcart_1(A_203, B_204, C_205, D_206)=k2_mcart_1(k1_mcart_1(D_206)) | ~m1_subset_1(D_206, k3_zfmisc_1(A_203, B_204, C_205)) | k1_xboole_0=C_205 | k1_xboole_0=B_204 | k1_xboole_0=A_203)), inference(cnfTransformation, [status(thm)], [f_109])).
% 23.02/14.58  tff(c_765, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_64, c_741])).
% 23.02/14.58  tff(c_774, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_60, c_58, c_56, c_765])).
% 23.02/14.58  tff(c_6756, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_6363])).
% 23.02/14.58  tff(c_202, plain, (![A_117, B_118, C_119]: (r2_hidden(k1_mcart_1(A_117), B_118) | ~r2_hidden(A_117, k2_zfmisc_1(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.02/14.58  tff(c_4164, plain, (![A_388, A_389, B_390, C_391]: (r2_hidden(k1_mcart_1(A_388), k2_zfmisc_1(A_389, B_390)) | ~r2_hidden(A_388, k3_zfmisc_1(A_389, B_390, C_391)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_202])).
% 23.02/14.58  tff(c_153987, plain, (![A_3662, A_3663, B_3664, C_3665]: (r2_hidden(k1_mcart_1(A_3662), k2_zfmisc_1(A_3663, B_3664)) | v1_xboole_0(k3_zfmisc_1(A_3663, B_3664, C_3665)) | ~m1_subset_1(A_3662, k3_zfmisc_1(A_3663, B_3664, C_3665)))), inference(resolution, [status(thm)], [c_10, c_4164])).
% 23.02/14.58  tff(c_154136, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_153987])).
% 23.02/14.58  tff(c_154150, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_6756, c_154136])).
% 23.02/14.58  tff(c_30, plain, (![A_36, B_37]: (k4_tarski(k1_mcart_1(A_36), k2_mcart_1(A_36))=A_36 | ~r2_hidden(A_36, B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_73])).
% 23.02/14.58  tff(c_154156, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_7')), k2_mcart_1(k1_mcart_1('#skF_7')))=k1_mcart_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_154150, c_30])).
% 23.02/14.58  tff(c_154168, plain, (k4_tarski(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))=k1_mcart_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_719, c_774, c_154156])).
% 23.02/14.58  tff(c_14, plain, (![A_11, B_12, C_13]: (k4_tarski(k4_tarski(A_11, B_12), C_13)=k3_mcart_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.02/14.58  tff(c_155156, plain, (![C_3692]: (k3_mcart_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), C_3692)=k4_tarski(k1_mcart_1('#skF_7'), C_3692))), inference(superposition, [status(thm), theory('equality')], [c_154168, c_14])).
% 23.02/14.58  tff(c_62, plain, (![H_78, F_72, G_76]: (H_78='#skF_6' | k3_mcart_1(F_72, G_76, H_78)!='#skF_7' | ~m1_subset_1(H_78, '#skF_5') | ~m1_subset_1(G_76, '#skF_4') | ~m1_subset_1(F_72, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 23.02/14.58  tff(c_155165, plain, (![C_3692]: (C_3692='#skF_6' | k4_tarski(k1_mcart_1('#skF_7'), C_3692)!='#skF_7' | ~m1_subset_1(C_3692, '#skF_5') | ~m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_155156, c_62])).
% 23.02/14.58  tff(c_156922, plain, (~m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(splitLeft, [status(thm)], [c_155165])).
% 23.02/14.58  tff(c_156925, plain, (~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_156922])).
% 23.02/14.58  tff(c_156929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_156925])).
% 23.02/14.58  tff(c_156930, plain, (![C_3692]: (~m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4') | C_3692='#skF_6' | k4_tarski(k1_mcart_1('#skF_7'), C_3692)!='#skF_7' | ~m1_subset_1(C_3692, '#skF_5'))), inference(splitRight, [status(thm)], [c_155165])).
% 23.02/14.58  tff(c_156937, plain, (~m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4')), inference(splitLeft, [status(thm)], [c_156930])).
% 23.02/14.58  tff(c_156940, plain, (~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_156937])).
% 23.02/14.58  tff(c_156944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_156940])).
% 23.02/14.58  tff(c_156952, plain, (![C_3704]: (C_3704='#skF_6' | k4_tarski(k1_mcart_1('#skF_7'), C_3704)!='#skF_7' | ~m1_subset_1(C_3704, '#skF_5'))), inference(splitRight, [status(thm)], [c_156930])).
% 23.02/14.58  tff(c_156955, plain, (k2_mcart_1('#skF_7')='#skF_6' | ~m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6755, c_156952])).
% 23.02/14.58  tff(c_156958, plain, (k2_mcart_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_609, c_156955])).
% 23.02/14.58  tff(c_156960, plain, $false, inference(negUnitSimplification, [status(thm)], [c_601, c_156958])).
% 23.02/14.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.02/14.58  
% 23.02/14.58  Inference rules
% 23.02/14.58  ----------------------
% 23.02/14.58  #Ref     : 0
% 23.02/14.58  #Sup     : 40359
% 23.02/14.58  #Fact    : 0
% 23.02/14.58  #Define  : 0
% 23.02/14.58  #Split   : 8
% 23.02/14.58  #Chain   : 0
% 23.02/14.58  #Close   : 0
% 23.02/14.58  
% 23.02/14.58  Ordering : KBO
% 23.02/14.58  
% 23.02/14.58  Simplification rules
% 23.02/14.58  ----------------------
% 23.02/14.58  #Subsume      : 3619
% 23.02/14.58  #Demod        : 37854
% 23.02/14.58  #Tautology    : 32227
% 23.02/14.58  #SimpNegUnit  : 298
% 23.02/14.58  #BackRed      : 14
% 23.02/14.58  
% 23.02/14.58  #Partial instantiations: 235
% 23.02/14.58  #Strategies tried      : 1
% 23.02/14.58  
% 23.02/14.58  Timing (in seconds)
% 23.02/14.58  ----------------------
% 23.02/14.58  Preprocessing        : 0.33
% 23.26/14.58  Parsing              : 0.17
% 23.26/14.58  CNF conversion       : 0.03
% 23.26/14.58  Main loop            : 13.47
% 23.26/14.58  Inferencing          : 2.81
% 23.26/14.58  Reduction            : 3.97
% 23.26/14.58  Demodulation         : 2.91
% 23.26/14.58  BG Simplification    : 0.27
% 23.26/14.58  Subsumption          : 5.85
% 23.26/14.58  Abstraction          : 0.46
% 23.26/14.58  MUC search           : 0.00
% 23.26/14.58  Cooper               : 0.00
% 23.26/14.58  Total                : 13.84
% 23.26/14.58  Index Insertion      : 0.00
% 23.26/14.58  Index Deletion       : 0.00
% 23.26/14.58  Index Matching       : 0.00
% 23.26/14.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
