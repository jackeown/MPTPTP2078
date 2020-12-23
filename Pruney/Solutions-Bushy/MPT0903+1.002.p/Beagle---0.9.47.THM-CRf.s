%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0903+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:03 EST 2020

% Result     : Theorem 33.11s
% Output     : CNFRefutation 33.21s
% Verified   : 
% Statistics : Number of formulae       :  162 (1218 expanded)
%              Number of leaves         :   41 ( 394 expanded)
%              Depth                    :   12
%              Number of atoms          :  335 (3840 expanded)
%              Number of equality atoms :  158 (1252 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ ( ~ r1_tarski(A,k4_zfmisc_1(A,B,C,D))
            & ~ r1_tarski(A,k4_zfmisc_1(B,C,D,A))
            & ~ r1_tarski(A,k4_zfmisc_1(C,D,A,B))
            & ~ r1_tarski(A,k4_zfmisc_1(D,A,B,C)) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_136,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_63,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

tff(f_25,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_38,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(f_91,axiom,(
    ! [A,B,C,D] : k3_zfmisc_1(k2_zfmisc_1(A,B),C,D) = k4_zfmisc_1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_tarski(A,k3_zfmisc_1(A,B,C))
          & ~ r1_tarski(A,k3_zfmisc_1(B,C,A))
          & ~ r1_tarski(A,k3_zfmisc_1(C,A,B)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_mcart_1)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_58,plain,
    ( r1_tarski('#skF_3',k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5'))
    | r1_tarski('#skF_3',k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4'))
    | r1_tarski('#skF_3',k4_zfmisc_1('#skF_4','#skF_5','#skF_6','#skF_3'))
    | r1_tarski('#skF_3',k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_95,plain,(
    r1_tarski('#skF_3',k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_16,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_219,plain,(
    ! [A_105,C_106,B_107] :
      ( m1_subset_1(A_105,C_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(C_106))
      | ~ r2_hidden(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_435,plain,(
    ! [A_138,B_139,A_140] :
      ( m1_subset_1(A_138,B_139)
      | ~ r2_hidden(A_138,A_140)
      | ~ r1_tarski(A_140,B_139) ) ),
    inference(resolution,[status(thm)],[c_26,c_219])).

tff(c_639,plain,(
    ! [A_174,B_175,B_176] :
      ( m1_subset_1(A_174,B_175)
      | ~ r1_tarski(B_176,B_175)
      | v1_xboole_0(B_176)
      | ~ m1_subset_1(A_174,B_176) ) ),
    inference(resolution,[status(thm)],[c_16,c_435])).

tff(c_655,plain,(
    ! [A_174] :
      ( m1_subset_1(A_174,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_174,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_95,c_639])).

tff(c_689,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_655])).

tff(c_54,plain,(
    ! [A_66] :
      ( k1_xboole_0 = A_66
      | ~ v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_692,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_689,c_54])).

tff(c_696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_692])).

tff(c_698,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_18,plain,(
    ! [A_22] :
      ( r2_hidden('#skF_2'(A_22),A_22)
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_441,plain,(
    ! [A_22,B_139] :
      ( m1_subset_1('#skF_2'(A_22),B_139)
      | ~ r1_tarski(A_22,B_139)
      | k1_xboole_0 = A_22 ) ),
    inference(resolution,[status(thm)],[c_18,c_435])).

tff(c_8,plain,(
    ! [E_12,D_11,A_8,C_10,B_9] :
      ( m1_subset_1(k8_mcart_1(A_8,B_9,C_10,D_11,E_12),A_8)
      | ~ m1_subset_1(E_12,k4_zfmisc_1(A_8,B_9,C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    ! [D_63,A_60,C_62,E_65,B_61] :
      ( k4_mcart_1(k8_mcart_1(A_60,B_61,C_62,D_63,E_65),k9_mcart_1(A_60,B_61,C_62,D_63,E_65),k10_mcart_1(A_60,B_61,C_62,D_63,E_65),k11_mcart_1(A_60,B_61,C_62,D_63,E_65)) = E_65
      | ~ m1_subset_1(E_65,k4_zfmisc_1(A_60,B_61,C_62,D_63))
      | k1_xboole_0 = D_63
      | k1_xboole_0 = C_62
      | k1_xboole_0 = B_61
      | k1_xboole_0 = A_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_497,plain,(
    ! [C_158,D_155,A_154,E_157,F_156] :
      ( ~ r2_hidden(C_158,A_154)
      | k4_mcart_1(C_158,D_155,E_157,F_156) != '#skF_2'(A_154)
      | k1_xboole_0 = A_154 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1162,plain,(
    ! [A_241,B_240,E_239,D_238,F_237] :
      ( k4_mcart_1(A_241,D_238,E_239,F_237) != '#skF_2'(B_240)
      | k1_xboole_0 = B_240
      | v1_xboole_0(B_240)
      | ~ m1_subset_1(A_241,B_240) ) ),
    inference(resolution,[status(thm)],[c_16,c_497])).

tff(c_7702,plain,(
    ! [A_634,E_636,B_633,D_632,C_631,B_635] :
      ( E_636 != '#skF_2'(B_635)
      | k1_xboole_0 = B_635
      | v1_xboole_0(B_635)
      | ~ m1_subset_1(k8_mcart_1(A_634,B_633,C_631,D_632,E_636),B_635)
      | ~ m1_subset_1(E_636,k4_zfmisc_1(A_634,B_633,C_631,D_632))
      | k1_xboole_0 = D_632
      | k1_xboole_0 = C_631
      | k1_xboole_0 = B_633
      | k1_xboole_0 = A_634 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1162])).

tff(c_7796,plain,(
    ! [B_639,C_640,E_638,D_641,A_637] :
      ( E_638 != '#skF_2'(A_637)
      | v1_xboole_0(A_637)
      | k1_xboole_0 = D_641
      | k1_xboole_0 = C_640
      | k1_xboole_0 = B_639
      | k1_xboole_0 = A_637
      | ~ m1_subset_1(E_638,k4_zfmisc_1(A_637,B_639,C_640,D_641)) ) ),
    inference(resolution,[status(thm)],[c_8,c_7702])).

tff(c_51190,plain,(
    ! [B_2120,D_2124,C_2122,A_2123,A_2121] :
      ( '#skF_2'(A_2123) != '#skF_2'(A_2121)
      | v1_xboole_0(A_2123)
      | k1_xboole_0 = D_2124
      | k1_xboole_0 = C_2122
      | k1_xboole_0 = B_2120
      | k1_xboole_0 = A_2123
      | ~ r1_tarski(A_2121,k4_zfmisc_1(A_2123,B_2120,C_2122,D_2124))
      | k1_xboole_0 = A_2121 ) ),
    inference(resolution,[status(thm)],[c_441,c_7796])).

tff(c_51297,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_95,c_51190])).

tff(c_51343,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_698,c_51297])).

tff(c_51346,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_51343])).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_25])).

tff(c_12,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_51865,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51346,c_59])).

tff(c_46,plain,(
    ! [A_53,C_55,D_56] : k4_zfmisc_1(A_53,k1_xboole_0,C_55,D_56) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_51859,plain,(
    ! [A_53,C_55,D_56] : k4_zfmisc_1(A_53,'#skF_4',C_55,D_56) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51346,c_51346,c_46])).

tff(c_206,plain,(
    ! [C_102,B_103,A_104] :
      ( ~ v1_xboole_0(C_102)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(C_102))
      | ~ r2_hidden(A_104,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_345,plain,(
    ! [B_118,A_119,A_120] :
      ( ~ v1_xboole_0(B_118)
      | ~ r2_hidden(A_119,A_120)
      | ~ r1_tarski(A_120,B_118) ) ),
    inference(resolution,[status(thm)],[c_26,c_206])).

tff(c_352,plain,(
    ! [B_121,A_122] :
      ( ~ v1_xboole_0(B_121)
      | ~ r1_tarski(A_122,B_121)
      | k1_xboole_0 = A_122 ) ),
    inference(resolution,[status(thm)],[c_18,c_345])).

tff(c_361,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_95,c_352])).

tff(c_373,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_361])).

tff(c_52574,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51859,c_373])).

tff(c_52578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51865,c_52574])).

tff(c_52579,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_51343])).

tff(c_52581,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_52579])).

tff(c_53101,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52581,c_59])).

tff(c_42,plain,(
    ! [A_53,B_54,C_55] : k4_zfmisc_1(A_53,B_54,C_55,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_53096,plain,(
    ! [A_53,B_54,C_55] : k4_zfmisc_1(A_53,B_54,C_55,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52581,c_52581,c_42])).

tff(c_53521,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53096,c_373])).

tff(c_53525,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53101,c_53521])).

tff(c_53526,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52579])).

tff(c_44,plain,(
    ! [A_53,B_54,D_56] : k4_zfmisc_1(A_53,B_54,k1_xboole_0,D_56) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_54044,plain,(
    ! [A_53,B_54,D_56] : k4_zfmisc_1(A_53,B_54,'#skF_5',D_56) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53526,c_53526,c_44])).

tff(c_697,plain,(
    ! [A_174] :
      ( m1_subset_1(A_174,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(A_174,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_655])).

tff(c_7748,plain,(
    ! [A_634,E_636,B_633,D_632,C_631] :
      ( E_636 != '#skF_2'(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6'))
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = k1_xboole_0
      | v1_xboole_0(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_subset_1(E_636,k4_zfmisc_1(A_634,B_633,C_631,D_632))
      | k1_xboole_0 = D_632
      | k1_xboole_0 = C_631
      | k1_xboole_0 = B_633
      | k1_xboole_0 = A_634
      | ~ m1_subset_1(k8_mcart_1(A_634,B_633,C_631,D_632,E_636),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_697,c_7702])).

tff(c_7792,plain,(
    ! [A_634,E_636,B_633,D_632,C_631] :
      ( E_636 != '#skF_2'(k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6'))
      | k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = k1_xboole_0
      | ~ m1_subset_1(E_636,k4_zfmisc_1(A_634,B_633,C_631,D_632))
      | k1_xboole_0 = D_632
      | k1_xboole_0 = C_631
      | k1_xboole_0 = B_633
      | k1_xboole_0 = A_634
      | ~ m1_subset_1(k8_mcart_1(A_634,B_633,C_631,D_632,E_636),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_373,c_7748])).

tff(c_8003,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7792])).

tff(c_8005,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8003,c_373])).

tff(c_8009,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_8005])).

tff(c_8011,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7792])).

tff(c_53898,plain,(
    k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53526,c_8011])).

tff(c_54853,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54044,c_53898])).

tff(c_54854,plain,
    ( r1_tarski('#skF_3',k4_zfmisc_1('#skF_4','#skF_5','#skF_6','#skF_3'))
    | r1_tarski('#skF_3',k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4'))
    | r1_tarski('#skF_3',k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54922,plain,(
    r1_tarski('#skF_3',k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_54854])).

tff(c_55104,plain,(
    ! [A_2278,C_2279,B_2280] :
      ( m1_subset_1(A_2278,C_2279)
      | ~ m1_subset_1(B_2280,k1_zfmisc_1(C_2279))
      | ~ r2_hidden(A_2278,B_2280) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_55135,plain,(
    ! [A_2283,B_2284,A_2285] :
      ( m1_subset_1(A_2283,B_2284)
      | ~ r2_hidden(A_2283,A_2285)
      | ~ r1_tarski(A_2285,B_2284) ) ),
    inference(resolution,[status(thm)],[c_26,c_55104])).

tff(c_55363,plain,(
    ! [A_2314,B_2315,B_2316] :
      ( m1_subset_1(A_2314,B_2315)
      | ~ r1_tarski(B_2316,B_2315)
      | v1_xboole_0(B_2316)
      | ~ m1_subset_1(A_2314,B_2316) ) ),
    inference(resolution,[status(thm)],[c_16,c_55135])).

tff(c_55377,plain,(
    ! [A_2314] :
      ( m1_subset_1(A_2314,k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5'))
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_2314,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54922,c_55363])).

tff(c_55406,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_55377])).

tff(c_55409,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_55406,c_54])).

tff(c_55413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_55409])).

tff(c_55415,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_55377])).

tff(c_55141,plain,(
    ! [A_22,B_2284] :
      ( m1_subset_1('#skF_2'(A_22),B_2284)
      | ~ r1_tarski(A_22,B_2284)
      | k1_xboole_0 = A_22 ) ),
    inference(resolution,[status(thm)],[c_18,c_55135])).

tff(c_10,plain,(
    ! [E_17,A_13,B_14,C_15,D_16] :
      ( m1_subset_1(k9_mcart_1(A_13,B_14,C_15,D_16,E_17),B_14)
      | ~ m1_subset_1(E_17,k4_zfmisc_1(A_13,B_14,C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_55450,plain,(
    ! [A_2329,D_2330,F_2331,E_2332,C_2333] :
      ( ~ r2_hidden(D_2330,A_2329)
      | k4_mcart_1(C_2333,D_2330,E_2332,F_2331) != '#skF_2'(A_2329)
      | k1_xboole_0 = A_2329 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_55923,plain,(
    ! [C_2399,B_2401,A_2402,F_2403,E_2400] :
      ( k4_mcart_1(C_2399,A_2402,E_2400,F_2403) != '#skF_2'(B_2401)
      | k1_xboole_0 = B_2401
      | v1_xboole_0(B_2401)
      | ~ m1_subset_1(A_2402,B_2401) ) ),
    inference(resolution,[status(thm)],[c_16,c_55450])).

tff(c_62618,plain,(
    ! [E_2808,B_2805,C_2803,D_2804,B_2807,A_2806] :
      ( E_2808 != '#skF_2'(B_2807)
      | k1_xboole_0 = B_2807
      | v1_xboole_0(B_2807)
      | ~ m1_subset_1(k9_mcart_1(A_2806,B_2805,C_2803,D_2804,E_2808),B_2807)
      | ~ m1_subset_1(E_2808,k4_zfmisc_1(A_2806,B_2805,C_2803,D_2804))
      | k1_xboole_0 = D_2804
      | k1_xboole_0 = C_2803
      | k1_xboole_0 = B_2805
      | k1_xboole_0 = A_2806 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_55923])).

tff(c_62920,plain,(
    ! [C_2819,B_2816,A_2818,D_2815,E_2817] :
      ( E_2817 != '#skF_2'(B_2816)
      | v1_xboole_0(B_2816)
      | k1_xboole_0 = D_2815
      | k1_xboole_0 = C_2819
      | k1_xboole_0 = B_2816
      | k1_xboole_0 = A_2818
      | ~ m1_subset_1(E_2817,k4_zfmisc_1(A_2818,B_2816,C_2819,D_2815)) ) ),
    inference(resolution,[status(thm)],[c_10,c_62618])).

tff(c_109188,plain,(
    ! [B_4336,C_4334,A_4335,D_4333,A_4332] :
      ( '#skF_2'(B_4336) != '#skF_2'(A_4332)
      | v1_xboole_0(B_4336)
      | k1_xboole_0 = D_4333
      | k1_xboole_0 = C_4334
      | k1_xboole_0 = B_4336
      | k1_xboole_0 = A_4335
      | ~ r1_tarski(A_4332,k4_zfmisc_1(A_4335,B_4336,C_4334,D_4333))
      | k1_xboole_0 = A_4332 ) ),
    inference(resolution,[status(thm)],[c_55141,c_62920])).

tff(c_109299,plain,
    ( v1_xboole_0('#skF_3')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54922,c_109188])).

tff(c_109346,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_55415,c_109299])).

tff(c_109349,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_109346])).

tff(c_109881,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109349,c_59])).

tff(c_48,plain,(
    ! [B_54,C_55,D_56] : k4_zfmisc_1(k1_xboole_0,B_54,C_55,D_56) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_109874,plain,(
    ! [B_54,C_55,D_56] : k4_zfmisc_1('#skF_6',B_54,C_55,D_56) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109349,c_109349,c_48])).

tff(c_54952,plain,(
    ! [C_2261,B_2262,A_2263] :
      ( ~ v1_xboole_0(C_2261)
      | ~ m1_subset_1(B_2262,k1_zfmisc_1(C_2261))
      | ~ r2_hidden(A_2263,B_2262) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_55074,plain,(
    ! [B_2273,A_2274,A_2275] :
      ( ~ v1_xboole_0(B_2273)
      | ~ r2_hidden(A_2274,A_2275)
      | ~ r1_tarski(A_2275,B_2273) ) ),
    inference(resolution,[status(thm)],[c_26,c_54952])).

tff(c_55081,plain,(
    ! [B_2276,A_2277] :
      ( ~ v1_xboole_0(B_2276)
      | ~ r1_tarski(A_2277,B_2276)
      | k1_xboole_0 = A_2277 ) ),
    inference(resolution,[status(thm)],[c_18,c_55074])).

tff(c_55087,plain,
    ( ~ v1_xboole_0(k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54922,c_55081])).

tff(c_55098,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_55087])).

tff(c_110273,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109874,c_55098])).

tff(c_110277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109881,c_110273])).

tff(c_110278,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_109346])).

tff(c_110280,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_110278])).

tff(c_110813,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110280,c_59])).

tff(c_110808,plain,(
    ! [A_53,B_54,C_55] : k4_zfmisc_1(A_53,B_54,C_55,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110280,c_110280,c_42])).

tff(c_111293,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110808,c_55098])).

tff(c_111297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110813,c_111293])).

tff(c_111298,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_110278])).

tff(c_111829,plain,(
    ! [A_53,B_54,D_56] : k4_zfmisc_1(A_53,B_54,'#skF_4',D_56) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111298,c_111298,c_44])).

tff(c_55414,plain,(
    ! [A_2314] :
      ( m1_subset_1(A_2314,k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(A_2314,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_55377])).

tff(c_55381,plain,(
    ! [D_2318,C_2321,E_2320,F_2319,A_2317] :
      ( ~ r2_hidden(C_2321,A_2317)
      | k4_mcart_1(C_2321,D_2318,E_2320,F_2319) != '#skF_2'(A_2317)
      | k1_xboole_0 = A_2317 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_55918,plain,(
    ! [B_2395,A_2396,E_2397,D_2394,F_2398] :
      ( k4_mcart_1(A_2396,D_2394,E_2397,F_2398) != '#skF_2'(B_2395)
      | k1_xboole_0 = B_2395
      | v1_xboole_0(B_2395)
      | ~ m1_subset_1(A_2396,B_2395) ) ),
    inference(resolution,[status(thm)],[c_16,c_55381])).

tff(c_62201,plain,(
    ! [B_2792,E_2794,C_2789,D_2791,A_2793,B_2790] :
      ( E_2794 != '#skF_2'(B_2790)
      | k1_xboole_0 = B_2790
      | v1_xboole_0(B_2790)
      | ~ m1_subset_1(k8_mcart_1(A_2793,B_2792,C_2789,D_2791,E_2794),B_2790)
      | ~ m1_subset_1(E_2794,k4_zfmisc_1(A_2793,B_2792,C_2789,D_2791))
      | k1_xboole_0 = D_2791
      | k1_xboole_0 = C_2789
      | k1_xboole_0 = B_2792
      | k1_xboole_0 = A_2793 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_55918])).

tff(c_62250,plain,(
    ! [B_2792,E_2794,C_2789,D_2791,A_2793] :
      ( E_2794 != '#skF_2'(k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5'))
      | k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5') = k1_xboole_0
      | v1_xboole_0(k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(E_2794,k4_zfmisc_1(A_2793,B_2792,C_2789,D_2791))
      | k1_xboole_0 = D_2791
      | k1_xboole_0 = C_2789
      | k1_xboole_0 = B_2792
      | k1_xboole_0 = A_2793
      | ~ m1_subset_1(k8_mcart_1(A_2793,B_2792,C_2789,D_2791,E_2794),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_55414,c_62201])).

tff(c_62292,plain,(
    ! [B_2792,E_2794,C_2789,D_2791,A_2793] :
      ( E_2794 != '#skF_2'(k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5'))
      | k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5') = k1_xboole_0
      | ~ m1_subset_1(E_2794,k4_zfmisc_1(A_2793,B_2792,C_2789,D_2791))
      | k1_xboole_0 = D_2791
      | k1_xboole_0 = C_2789
      | k1_xboole_0 = B_2792
      | k1_xboole_0 = A_2793
      | ~ m1_subset_1(k8_mcart_1(A_2793,B_2792,C_2789,D_2791,E_2794),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_55098,c_62250])).

tff(c_62761,plain,(
    k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62292])).

tff(c_62763,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62761,c_55098])).

tff(c_62767,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_62763])).

tff(c_62769,plain,(
    k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62292])).

tff(c_111682,plain,(
    k4_zfmisc_1('#skF_6','#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111298,c_62769])).

tff(c_112336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111829,c_111682])).

tff(c_112337,plain,
    ( r1_tarski('#skF_3',k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4'))
    | r1_tarski('#skF_3',k4_zfmisc_1('#skF_4','#skF_5','#skF_6','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54854])).

tff(c_112366,plain,(
    r1_tarski('#skF_3',k4_zfmisc_1('#skF_4','#skF_5','#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_112337])).

tff(c_112437,plain,(
    ! [A_4460,B_4461,C_4462,D_4463] : k3_zfmisc_1(k2_zfmisc_1(A_4460,B_4461),C_4462,D_4463) = k4_zfmisc_1(A_4460,B_4461,C_4462,D_4463) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_32,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_tarski(A_43,k3_zfmisc_1(B_44,C_45,A_43))
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_112620,plain,(
    ! [D_4490,A_4491,B_4492,C_4493] :
      ( ~ r1_tarski(D_4490,k4_zfmisc_1(A_4491,B_4492,C_4493,D_4490))
      | k1_xboole_0 = D_4490 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112437,c_32])).

tff(c_112627,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_112366,c_112620])).

tff(c_112647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_112627])).

tff(c_112648,plain,(
    r1_tarski('#skF_3',k4_zfmisc_1('#skF_5','#skF_6','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_112337])).

tff(c_112842,plain,(
    ! [A_4525,B_4526,C_4527,D_4528] : k3_zfmisc_1(k2_zfmisc_1(A_4525,B_4526),C_4527,D_4528) = k4_zfmisc_1(A_4525,B_4526,C_4527,D_4528) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    ! [A_43,C_45,B_44] :
      ( ~ r1_tarski(A_43,k3_zfmisc_1(C_45,A_43,B_44))
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_112860,plain,(
    ! [C_4529,A_4530,B_4531,D_4532] :
      ( ~ r1_tarski(C_4529,k4_zfmisc_1(A_4530,B_4531,C_4529,D_4532))
      | k1_xboole_0 = C_4529 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112842,c_30])).

tff(c_112867,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_112648,c_112860])).

tff(c_112887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_112867])).

%------------------------------------------------------------------------------
