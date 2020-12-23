%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:03 EST 2020

% Result     : Theorem 17.24s
% Output     : CNFRefutation 17.24s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 304 expanded)
%              Number of leaves         :   43 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          :  199 ( 873 expanded)
%              Number of equality atoms :   99 ( 447 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_144,negated_conjecture,(
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

tff(f_105,axiom,(
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

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_85,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_63,axiom,(
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

tff(f_51,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_581,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( k7_mcart_1(A_163,B_164,C_165,D_166) = k2_mcart_1(D_166)
      | ~ m1_subset_1(D_166,k3_zfmisc_1(A_163,B_164,C_165))
      | k1_xboole_0 = C_165
      | k1_xboole_0 = B_164
      | k1_xboole_0 = A_163 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_605,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_62,c_581])).

tff(c_614,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_605])).

tff(c_52,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_615,plain,(
    k2_mcart_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_52])).

tff(c_22,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( m1_subset_1(k7_mcart_1(A_22,B_23,C_24,D_25),C_24)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_619,plain,
    ( m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5')
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_22])).

tff(c_623,plain,(
    m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_619])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    ! [A_54,B_55,D_57] : k4_zfmisc_1(A_54,B_55,k1_xboole_0,D_57) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_2'(A_31),A_31)
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_179,plain,(
    ! [A_101,C_102,B_103] :
      ( r2_hidden(k2_mcart_1(A_101),C_102)
      | ~ r2_hidden(A_101,k2_zfmisc_1(B_103,C_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_295,plain,(
    ! [B_130,C_131] :
      ( r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_130,C_131))),C_131)
      | k2_zfmisc_1(B_130,C_131) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_179])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_340,plain,(
    ! [C_137,B_138] :
      ( ~ v1_xboole_0(C_137)
      | k2_zfmisc_1(B_138,C_137) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_295,c_2])).

tff(c_344,plain,(
    ! [B_139] : k2_zfmisc_1(B_139,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_340])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] : k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),C_17) = k3_zfmisc_1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_383,plain,(
    ! [A_140,B_141] : k3_zfmisc_1(A_140,B_141,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_18])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20,D_21] : k2_zfmisc_1(k3_zfmisc_1(A_18,B_19,C_20),D_21) = k4_zfmisc_1(A_18,B_19,C_20,D_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_388,plain,(
    ! [A_140,B_141,D_21] : k4_zfmisc_1(A_140,B_141,k1_xboole_0,D_21) = k2_zfmisc_1(k1_xboole_0,D_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_20])).

tff(c_396,plain,(
    ! [D_21] : k2_zfmisc_1(k1_xboole_0,D_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_388])).

tff(c_192,plain,(
    ! [A_104,B_105,C_106] : k2_zfmisc_1(k2_zfmisc_1(A_104,B_105),C_106) = k3_zfmisc_1(A_104,B_105,C_106) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_202,plain,(
    ! [A_104,B_105,C_106] : v1_relat_1(k3_zfmisc_1(A_104,B_105,C_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_14])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_282,plain,(
    ! [A_128,B_129] :
      ( k4_tarski(k1_mcart_1(A_128),k2_mcart_1(A_128)) = A_128
      | ~ r2_hidden(A_128,B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7395,plain,(
    ! [A_460,B_461] :
      ( k4_tarski(k1_mcart_1(A_460),k2_mcart_1(A_460)) = A_460
      | ~ v1_relat_1(B_461)
      | v1_xboole_0(B_461)
      | ~ m1_subset_1(A_460,B_461) ) ),
    inference(resolution,[status(thm)],[c_12,c_282])).

tff(c_7413,plain,
    ( k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_3','#skF_4','#skF_5'))
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_62,c_7395])).

tff(c_7424,plain,
    ( k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_7413])).

tff(c_7425,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7424])).

tff(c_152,plain,(
    ! [A_92] :
      ( r2_hidden('#skF_2'(A_92),A_92)
      | k1_xboole_0 = A_92 ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_160,plain,(
    ! [A_92] :
      ( ~ v1_xboole_0(A_92)
      | k1_xboole_0 = A_92 ) ),
    inference(resolution,[status(thm)],[c_152,c_2])).

tff(c_7459,plain,(
    k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7425,c_160])).

tff(c_7524,plain,(
    ! [D_21] : k4_zfmisc_1('#skF_3','#skF_4','#skF_5',D_21) = k2_zfmisc_1(k1_xboole_0,D_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_7459,c_20])).

tff(c_7559,plain,(
    ! [D_462] : k4_zfmisc_1('#skF_3','#skF_4','#skF_5',D_462) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_7524])).

tff(c_42,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k4_zfmisc_1(A_54,B_55,C_56,D_57) != k1_xboole_0
      | k1_xboole_0 = D_57
      | k1_xboole_0 = C_56
      | k1_xboole_0 = B_55
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_7599,plain,(
    ! [D_462] :
      ( k1_xboole_0 = D_462
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7559,c_42])).

tff(c_7642,plain,(
    ! [D_463] : k1_xboole_0 = D_463 ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_7599])).

tff(c_8,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7788,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7642,c_8])).

tff(c_7833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_7788])).

tff(c_7834,plain,(
    k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7424])).

tff(c_664,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( k5_mcart_1(A_175,B_176,C_177,D_178) = k1_mcart_1(k1_mcart_1(D_178))
      | ~ m1_subset_1(D_178,k3_zfmisc_1(A_175,B_176,C_177))
      | k1_xboole_0 = C_177
      | k1_xboole_0 = B_176
      | k1_xboole_0 = A_175 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_688,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_62,c_664])).

tff(c_697,plain,(
    k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_688])).

tff(c_7835,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_7424])).

tff(c_227,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden(k1_mcart_1(A_113),B_114)
      | ~ r2_hidden(A_113,k2_zfmisc_1(B_114,C_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8244,plain,(
    ! [A_2203,B_2204,C_2205] :
      ( r2_hidden(k1_mcart_1(A_2203),B_2204)
      | v1_xboole_0(k2_zfmisc_1(B_2204,C_2205))
      | ~ m1_subset_1(A_2203,k2_zfmisc_1(B_2204,C_2205)) ) ),
    inference(resolution,[status(thm)],[c_12,c_227])).

tff(c_8287,plain,(
    ! [A_2203,A_15,B_16,C_17] :
      ( r2_hidden(k1_mcart_1(A_2203),k2_zfmisc_1(A_15,B_16))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_15,B_16),C_17))
      | ~ m1_subset_1(A_2203,k3_zfmisc_1(A_15,B_16,C_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_8244])).

tff(c_96996,plain,(
    ! [A_3318,A_3319,B_3320,C_3321] :
      ( r2_hidden(k1_mcart_1(A_3318),k2_zfmisc_1(A_3319,B_3320))
      | v1_xboole_0(k3_zfmisc_1(A_3319,B_3320,C_3321))
      | ~ m1_subset_1(A_3318,k3_zfmisc_1(A_3319,B_3320,C_3321)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8287])).

tff(c_97127,plain,
    ( r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_62,c_96996])).

tff(c_97148,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_7835,c_97127])).

tff(c_26,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden(k1_mcart_1(A_26),B_27)
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97156,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_97148,c_26])).

tff(c_97171,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_97156])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97211,plain,(
    m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_97171,c_10])).

tff(c_625,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( k6_mcart_1(A_167,B_168,C_169,D_170) = k2_mcart_1(k1_mcart_1(D_170))
      | ~ m1_subset_1(D_170,k3_zfmisc_1(A_167,B_168,C_169))
      | k1_xboole_0 = C_169
      | k1_xboole_0 = B_168
      | k1_xboole_0 = A_167 ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_649,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_62,c_625])).

tff(c_658,plain,(
    k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_649])).

tff(c_24,plain,(
    ! [A_26,C_28,B_27] :
      ( r2_hidden(k2_mcart_1(A_26),C_28)
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_97158,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_97148,c_24])).

tff(c_97173,plain,(
    r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_97158])).

tff(c_97233,plain,(
    m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_97173,c_10])).

tff(c_28,plain,(
    ! [A_29,B_30] :
      ( k4_tarski(k1_mcart_1(A_29),k2_mcart_1(A_29)) = A_29
      | ~ r2_hidden(A_29,B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_97154,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_7')),k2_mcart_1(k1_mcart_1('#skF_7'))) = k1_mcart_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_97148,c_28])).

tff(c_97169,plain,(
    k4_tarski(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')) = k1_mcart_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_658,c_697,c_97154])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : k4_tarski(k4_tarski(A_12,B_13),C_14) = k3_mcart_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_99059,plain,(
    ! [C_3371] : k3_mcart_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),C_3371) = k4_tarski(k1_mcart_1('#skF_7'),C_3371) ),
    inference(superposition,[status(thm),theory(equality)],[c_97169,c_16])).

tff(c_60,plain,(
    ! [H_71,F_65,G_69] :
      ( H_71 = '#skF_6'
      | k3_mcart_1(F_65,G_69,H_71) != '#skF_7'
      | ~ m1_subset_1(H_71,'#skF_5')
      | ~ m1_subset_1(G_69,'#skF_4')
      | ~ m1_subset_1(F_65,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_99066,plain,(
    ! [C_3371] :
      ( C_3371 = '#skF_6'
      | k4_tarski(k1_mcart_1('#skF_7'),C_3371) != '#skF_7'
      | ~ m1_subset_1(C_3371,'#skF_5')
      | ~ m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4')
      | ~ m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99059,c_60])).

tff(c_99075,plain,(
    ! [C_3372] :
      ( C_3372 = '#skF_6'
      | k4_tarski(k1_mcart_1('#skF_7'),C_3372) != '#skF_7'
      | ~ m1_subset_1(C_3372,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97211,c_97233,c_99066])).

tff(c_99078,plain,
    ( k2_mcart_1('#skF_7') = '#skF_6'
    | ~ m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7834,c_99075])).

tff(c_99081,plain,(
    k2_mcart_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_99078])).

tff(c_99083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_615,c_99081])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:00:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.24/9.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.24/9.76  
% 17.24/9.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.24/9.76  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 17.24/9.76  
% 17.24/9.76  %Foreground sorts:
% 17.24/9.76  
% 17.24/9.76  
% 17.24/9.76  %Background operators:
% 17.24/9.76  
% 17.24/9.76  
% 17.24/9.76  %Foreground operators:
% 17.24/9.76  tff('#skF_2', type, '#skF_2': $i > $i).
% 17.24/9.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.24/9.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.24/9.76  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 17.24/9.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 17.24/9.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.24/9.76  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 17.24/9.76  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 17.24/9.76  tff('#skF_7', type, '#skF_7': $i).
% 17.24/9.76  tff('#skF_5', type, '#skF_5': $i).
% 17.24/9.76  tff('#skF_6', type, '#skF_6': $i).
% 17.24/9.76  tff('#skF_3', type, '#skF_3': $i).
% 17.24/9.76  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 17.24/9.76  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 17.24/9.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.24/9.76  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 17.24/9.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.24/9.76  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 17.24/9.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.24/9.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.24/9.76  tff('#skF_4', type, '#skF_4': $i).
% 17.24/9.76  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 17.24/9.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.24/9.76  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 17.24/9.76  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 17.24/9.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.24/9.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.24/9.76  
% 17.24/9.78  tff(f_144, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 17.24/9.78  tff(f_105, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 17.24/9.78  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 17.24/9.78  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 17.24/9.78  tff(f_120, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 17.24/9.78  tff(f_85, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 17.24/9.78  tff(f_63, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 17.24/9.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 17.24/9.78  tff(f_51, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 17.24/9.78  tff(f_53, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 17.24/9.78  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 17.24/9.78  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 17.24/9.78  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 17.24/9.78  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 17.24/9.78  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 17.24/9.78  tff(f_49, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 17.24/9.78  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_144])).
% 17.24/9.78  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_144])).
% 17.24/9.78  tff(c_54, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_144])).
% 17.24/9.78  tff(c_62, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 17.24/9.78  tff(c_581, plain, (![A_163, B_164, C_165, D_166]: (k7_mcart_1(A_163, B_164, C_165, D_166)=k2_mcart_1(D_166) | ~m1_subset_1(D_166, k3_zfmisc_1(A_163, B_164, C_165)) | k1_xboole_0=C_165 | k1_xboole_0=B_164 | k1_xboole_0=A_163)), inference(cnfTransformation, [status(thm)], [f_105])).
% 17.24/9.78  tff(c_605, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_62, c_581])).
% 17.24/9.78  tff(c_614, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_605])).
% 17.24/9.78  tff(c_52, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_144])).
% 17.24/9.78  tff(c_615, plain, (k2_mcart_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_614, c_52])).
% 17.24/9.78  tff(c_22, plain, (![A_22, B_23, C_24, D_25]: (m1_subset_1(k7_mcart_1(A_22, B_23, C_24, D_25), C_24) | ~m1_subset_1(D_25, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 17.24/9.78  tff(c_619, plain, (m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5') | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_614, c_22])).
% 17.24/9.78  tff(c_623, plain, (m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_619])).
% 17.24/9.78  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.24/9.78  tff(c_46, plain, (![A_54, B_55, D_57]: (k4_zfmisc_1(A_54, B_55, k1_xboole_0, D_57)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_120])).
% 17.24/9.78  tff(c_30, plain, (![A_31]: (r2_hidden('#skF_2'(A_31), A_31) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_85])).
% 17.24/9.78  tff(c_179, plain, (![A_101, C_102, B_103]: (r2_hidden(k2_mcart_1(A_101), C_102) | ~r2_hidden(A_101, k2_zfmisc_1(B_103, C_102)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.24/9.78  tff(c_295, plain, (![B_130, C_131]: (r2_hidden(k2_mcart_1('#skF_2'(k2_zfmisc_1(B_130, C_131))), C_131) | k2_zfmisc_1(B_130, C_131)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_179])).
% 17.24/9.78  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.24/9.78  tff(c_340, plain, (![C_137, B_138]: (~v1_xboole_0(C_137) | k2_zfmisc_1(B_138, C_137)=k1_xboole_0)), inference(resolution, [status(thm)], [c_295, c_2])).
% 17.24/9.78  tff(c_344, plain, (![B_139]: (k2_zfmisc_1(B_139, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_340])).
% 17.24/9.78  tff(c_18, plain, (![A_15, B_16, C_17]: (k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), C_17)=k3_zfmisc_1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.24/9.78  tff(c_383, plain, (![A_140, B_141]: (k3_zfmisc_1(A_140, B_141, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_344, c_18])).
% 17.24/9.78  tff(c_20, plain, (![A_18, B_19, C_20, D_21]: (k2_zfmisc_1(k3_zfmisc_1(A_18, B_19, C_20), D_21)=k4_zfmisc_1(A_18, B_19, C_20, D_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.24/9.78  tff(c_388, plain, (![A_140, B_141, D_21]: (k4_zfmisc_1(A_140, B_141, k1_xboole_0, D_21)=k2_zfmisc_1(k1_xboole_0, D_21))), inference(superposition, [status(thm), theory('equality')], [c_383, c_20])).
% 17.24/9.78  tff(c_396, plain, (![D_21]: (k2_zfmisc_1(k1_xboole_0, D_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_388])).
% 17.24/9.78  tff(c_192, plain, (![A_104, B_105, C_106]: (k2_zfmisc_1(k2_zfmisc_1(A_104, B_105), C_106)=k3_zfmisc_1(A_104, B_105, C_106))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.24/9.78  tff(c_14, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.24/9.78  tff(c_202, plain, (![A_104, B_105, C_106]: (v1_relat_1(k3_zfmisc_1(A_104, B_105, C_106)))), inference(superposition, [status(thm), theory('equality')], [c_192, c_14])).
% 17.24/9.78  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.24/9.78  tff(c_282, plain, (![A_128, B_129]: (k4_tarski(k1_mcart_1(A_128), k2_mcart_1(A_128))=A_128 | ~r2_hidden(A_128, B_129) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.24/9.78  tff(c_7395, plain, (![A_460, B_461]: (k4_tarski(k1_mcart_1(A_460), k2_mcart_1(A_460))=A_460 | ~v1_relat_1(B_461) | v1_xboole_0(B_461) | ~m1_subset_1(A_460, B_461))), inference(resolution, [status(thm)], [c_12, c_282])).
% 17.24/9.78  tff(c_7413, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~v1_relat_1(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_7395])).
% 17.24/9.78  tff(c_7424, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_7413])).
% 17.24/9.78  tff(c_7425, plain, (v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_7424])).
% 17.24/9.78  tff(c_152, plain, (![A_92]: (r2_hidden('#skF_2'(A_92), A_92) | k1_xboole_0=A_92)), inference(cnfTransformation, [status(thm)], [f_85])).
% 17.24/9.78  tff(c_160, plain, (![A_92]: (~v1_xboole_0(A_92) | k1_xboole_0=A_92)), inference(resolution, [status(thm)], [c_152, c_2])).
% 17.24/9.78  tff(c_7459, plain, (k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_7425, c_160])).
% 17.24/9.78  tff(c_7524, plain, (![D_21]: (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', D_21)=k2_zfmisc_1(k1_xboole_0, D_21))), inference(superposition, [status(thm), theory('equality')], [c_7459, c_20])).
% 17.24/9.78  tff(c_7559, plain, (![D_462]: (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', D_462)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_396, c_7524])).
% 17.24/9.78  tff(c_42, plain, (![A_54, B_55, C_56, D_57]: (k4_zfmisc_1(A_54, B_55, C_56, D_57)!=k1_xboole_0 | k1_xboole_0=D_57 | k1_xboole_0=C_56 | k1_xboole_0=B_55 | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_120])).
% 17.24/9.78  tff(c_7599, plain, (![D_462]: (k1_xboole_0=D_462 | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7559, c_42])).
% 17.24/9.78  tff(c_7642, plain, (![D_463]: (k1_xboole_0=D_463)), inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_7599])).
% 17.24/9.78  tff(c_8, plain, (![A_5]: (~v1_xboole_0(k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.24/9.78  tff(c_7788, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7642, c_8])).
% 17.24/9.78  tff(c_7833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_7788])).
% 17.24/9.78  tff(c_7834, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(splitRight, [status(thm)], [c_7424])).
% 17.24/9.78  tff(c_664, plain, (![A_175, B_176, C_177, D_178]: (k5_mcart_1(A_175, B_176, C_177, D_178)=k1_mcart_1(k1_mcart_1(D_178)) | ~m1_subset_1(D_178, k3_zfmisc_1(A_175, B_176, C_177)) | k1_xboole_0=C_177 | k1_xboole_0=B_176 | k1_xboole_0=A_175)), inference(cnfTransformation, [status(thm)], [f_105])).
% 17.24/9.78  tff(c_688, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_62, c_664])).
% 17.24/9.78  tff(c_697, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_688])).
% 17.24/9.78  tff(c_7835, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_7424])).
% 17.24/9.78  tff(c_227, plain, (![A_113, B_114, C_115]: (r2_hidden(k1_mcart_1(A_113), B_114) | ~r2_hidden(A_113, k2_zfmisc_1(B_114, C_115)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.24/9.78  tff(c_8244, plain, (![A_2203, B_2204, C_2205]: (r2_hidden(k1_mcart_1(A_2203), B_2204) | v1_xboole_0(k2_zfmisc_1(B_2204, C_2205)) | ~m1_subset_1(A_2203, k2_zfmisc_1(B_2204, C_2205)))), inference(resolution, [status(thm)], [c_12, c_227])).
% 17.24/9.78  tff(c_8287, plain, (![A_2203, A_15, B_16, C_17]: (r2_hidden(k1_mcart_1(A_2203), k2_zfmisc_1(A_15, B_16)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_15, B_16), C_17)) | ~m1_subset_1(A_2203, k3_zfmisc_1(A_15, B_16, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_8244])).
% 17.24/9.78  tff(c_96996, plain, (![A_3318, A_3319, B_3320, C_3321]: (r2_hidden(k1_mcart_1(A_3318), k2_zfmisc_1(A_3319, B_3320)) | v1_xboole_0(k3_zfmisc_1(A_3319, B_3320, C_3321)) | ~m1_subset_1(A_3318, k3_zfmisc_1(A_3319, B_3320, C_3321)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8287])).
% 17.24/9.78  tff(c_97127, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_96996])).
% 17.24/9.78  tff(c_97148, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_7835, c_97127])).
% 17.24/9.78  tff(c_26, plain, (![A_26, B_27, C_28]: (r2_hidden(k1_mcart_1(A_26), B_27) | ~r2_hidden(A_26, k2_zfmisc_1(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.24/9.78  tff(c_97156, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')), '#skF_3')), inference(resolution, [status(thm)], [c_97148, c_26])).
% 17.24/9.78  tff(c_97171, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_697, c_97156])).
% 17.24/9.78  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 17.24/9.78  tff(c_97211, plain, (m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(resolution, [status(thm)], [c_97171, c_10])).
% 17.24/9.78  tff(c_625, plain, (![A_167, B_168, C_169, D_170]: (k6_mcart_1(A_167, B_168, C_169, D_170)=k2_mcart_1(k1_mcart_1(D_170)) | ~m1_subset_1(D_170, k3_zfmisc_1(A_167, B_168, C_169)) | k1_xboole_0=C_169 | k1_xboole_0=B_168 | k1_xboole_0=A_167)), inference(cnfTransformation, [status(thm)], [f_105])).
% 17.24/9.78  tff(c_649, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_62, c_625])).
% 17.24/9.78  tff(c_658, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_649])).
% 17.24/9.78  tff(c_24, plain, (![A_26, C_28, B_27]: (r2_hidden(k2_mcart_1(A_26), C_28) | ~r2_hidden(A_26, k2_zfmisc_1(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.24/9.78  tff(c_97158, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_4')), inference(resolution, [status(thm)], [c_97148, c_24])).
% 17.24/9.78  tff(c_97173, plain, (r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_658, c_97158])).
% 17.24/9.78  tff(c_97233, plain, (m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_97173, c_10])).
% 17.24/9.78  tff(c_28, plain, (![A_29, B_30]: (k4_tarski(k1_mcart_1(A_29), k2_mcart_1(A_29))=A_29 | ~r2_hidden(A_29, B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.24/9.78  tff(c_97154, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_7')), k2_mcart_1(k1_mcart_1('#skF_7')))=k1_mcart_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_97148, c_28])).
% 17.24/9.78  tff(c_97169, plain, (k4_tarski(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))=k1_mcart_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_658, c_697, c_97154])).
% 17.24/9.78  tff(c_16, plain, (![A_12, B_13, C_14]: (k4_tarski(k4_tarski(A_12, B_13), C_14)=k3_mcart_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.24/9.78  tff(c_99059, plain, (![C_3371]: (k3_mcart_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), C_3371)=k4_tarski(k1_mcart_1('#skF_7'), C_3371))), inference(superposition, [status(thm), theory('equality')], [c_97169, c_16])).
% 17.24/9.78  tff(c_60, plain, (![H_71, F_65, G_69]: (H_71='#skF_6' | k3_mcart_1(F_65, G_69, H_71)!='#skF_7' | ~m1_subset_1(H_71, '#skF_5') | ~m1_subset_1(G_69, '#skF_4') | ~m1_subset_1(F_65, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 17.24/9.78  tff(c_99066, plain, (![C_3371]: (C_3371='#skF_6' | k4_tarski(k1_mcart_1('#skF_7'), C_3371)!='#skF_7' | ~m1_subset_1(C_3371, '#skF_5') | ~m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_99059, c_60])).
% 17.24/9.78  tff(c_99075, plain, (![C_3372]: (C_3372='#skF_6' | k4_tarski(k1_mcart_1('#skF_7'), C_3372)!='#skF_7' | ~m1_subset_1(C_3372, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_97211, c_97233, c_99066])).
% 17.24/9.78  tff(c_99078, plain, (k2_mcart_1('#skF_7')='#skF_6' | ~m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7834, c_99075])).
% 17.24/9.78  tff(c_99081, plain, (k2_mcart_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_623, c_99078])).
% 17.24/9.78  tff(c_99083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_615, c_99081])).
% 17.24/9.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.24/9.78  
% 17.24/9.78  Inference rules
% 17.24/9.78  ----------------------
% 17.24/9.78  #Ref     : 0
% 17.24/9.78  #Sup     : 25551
% 17.24/9.78  #Fact    : 0
% 17.24/9.78  #Define  : 0
% 17.24/9.78  #Split   : 6
% 17.24/9.78  #Chain   : 0
% 17.24/9.78  #Close   : 0
% 17.24/9.78  
% 17.24/9.78  Ordering : KBO
% 17.24/9.78  
% 17.24/9.78  Simplification rules
% 17.24/9.78  ----------------------
% 17.24/9.78  #Subsume      : 2450
% 17.24/9.78  #Demod        : 22282
% 17.24/9.78  #Tautology    : 19564
% 17.24/9.78  #SimpNegUnit  : 152
% 17.24/9.78  #BackRed      : 11
% 17.24/9.78  
% 17.24/9.78  #Partial instantiations: 240
% 17.24/9.78  #Strategies tried      : 1
% 17.24/9.78  
% 17.24/9.78  Timing (in seconds)
% 17.24/9.78  ----------------------
% 17.24/9.78  Preprocessing        : 0.34
% 17.24/9.78  Parsing              : 0.19
% 17.24/9.78  CNF conversion       : 0.02
% 17.24/9.78  Main loop            : 8.60
% 17.24/9.78  Inferencing          : 1.85
% 17.24/9.78  Reduction            : 2.58
% 17.24/9.78  Demodulation         : 1.91
% 17.24/9.78  BG Simplification    : 0.19
% 17.24/9.78  Subsumption          : 3.57
% 17.24/9.78  Abstraction          : 0.27
% 17.24/9.78  MUC search           : 0.00
% 17.24/9.78  Cooper               : 0.00
% 17.24/9.78  Total                : 8.99
% 17.24/9.78  Index Insertion      : 0.00
% 17.24/9.78  Index Deletion       : 0.00
% 17.24/9.78  Index Matching       : 0.00
% 17.24/9.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
