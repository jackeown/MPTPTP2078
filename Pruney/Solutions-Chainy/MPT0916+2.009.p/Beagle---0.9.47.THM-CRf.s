%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:11 EST 2020

% Result     : Theorem 9.62s
% Output     : CNFRefutation 10.08s
% Verified   : 
% Statistics : Number of formulae       :  385 (1614 expanded)
%              Number of leaves         :   45 ( 527 expanded)
%              Depth                    :   14
%              Number of atoms          :  590 (4096 expanded)
%              Number of equality atoms :  223 (1110 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_132,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_111,axiom,(
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

tff(f_73,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_85,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_16,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_3'(A_40),A_40)
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_58,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_11107,plain,(
    ! [A_713,B_714,C_715,D_716] :
      ( k7_mcart_1(A_713,B_714,C_715,D_716) = k2_mcart_1(D_716)
      | ~ m1_subset_1(D_716,k3_zfmisc_1(A_713,B_714,C_715))
      | k1_xboole_0 = C_715
      | k1_xboole_0 = B_714
      | k1_xboole_0 = A_713 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_11111,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_11107])).

tff(c_11183,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11111])).

tff(c_26,plain,(
    ! [A_22] : r1_xboole_0(A_22,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_70,plain,(
    ! [B_79,A_80] :
      ( r1_xboole_0(B_79,A_80)
      | ~ r1_xboole_0(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ! [A_22] : r1_xboole_0(k1_xboole_0,A_22) ),
    inference(resolution,[status(thm)],[c_26,c_70])).

tff(c_10346,plain,(
    ! [A_649,B_650] :
      ( k4_xboole_0(A_649,B_650) = A_649
      | ~ r1_xboole_0(A_649,B_650) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10360,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_10346])).

tff(c_10480,plain,(
    ! [A_661,C_662,B_663] :
      ( r1_xboole_0(A_661,C_662)
      | ~ r1_tarski(A_661,k4_xboole_0(B_663,C_662)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10499,plain,(
    ! [A_664,A_665] :
      ( r1_xboole_0(A_664,A_665)
      | ~ r1_tarski(A_664,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10360,c_10480])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10506,plain,(
    ! [A_665,A_664] :
      ( r1_xboole_0(A_665,A_664)
      | ~ r1_tarski(A_664,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10499,c_6])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_103,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(A_89,B_90)
      | ~ m1_subset_1(A_89,k1_zfmisc_1(B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_119,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_103])).

tff(c_10304,plain,(
    ! [A_646,B_647] :
      ( k3_xboole_0(A_646,B_647) = A_646
      | ~ r1_tarski(A_646,B_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10317,plain,(
    k3_xboole_0('#skF_7','#skF_4') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_119,c_10304])).

tff(c_10527,plain,(
    ! [A_672,B_673,C_674] :
      ( ~ r1_xboole_0(A_672,B_673)
      | ~ r2_hidden(C_674,k3_xboole_0(A_672,B_673)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10533,plain,(
    ! [C_674] :
      ( ~ r1_xboole_0('#skF_7','#skF_4')
      | ~ r2_hidden(C_674,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10317,c_10527])).

tff(c_10592,plain,(
    ~ r1_xboole_0('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10533])).

tff(c_10605,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10506,c_10592])).

tff(c_11198,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11183,c_10605])).

tff(c_11214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_11198])).

tff(c_11215,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_11111])).

tff(c_11657,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_11215])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5793,plain,(
    ! [A_386,B_387,C_388] :
      ( r2_hidden(k1_mcart_1(A_386),B_387)
      | ~ r2_hidden(A_386,k2_zfmisc_1(B_387,C_388)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7730,plain,(
    ! [B_499,C_500] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_499,C_500))),B_499)
      | v1_xboole_0(k2_zfmisc_1(B_499,C_500)) ) ),
    inference(resolution,[status(thm)],[c_4,c_5793])).

tff(c_54,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9')
    | ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8')
    | ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_120,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_955,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k7_mcart_1(A_160,B_161,C_162,D_163) = k2_mcart_1(D_163)
      | ~ m1_subset_1(D_163,k3_zfmisc_1(A_160,B_161,C_162))
      | k1_xboole_0 = C_162
      | k1_xboole_0 = B_161
      | k1_xboole_0 = A_160 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_959,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_955])).

tff(c_1004,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_959])).

tff(c_163,plain,(
    ! [A_96,B_97] :
      ( k4_xboole_0(A_96,B_97) = A_96
      | ~ r1_xboole_0(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_181,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_163])).

tff(c_291,plain,(
    ! [A_106,C_107,B_108] :
      ( r1_xboole_0(A_106,C_107)
      | ~ r1_tarski(A_106,k4_xboole_0(B_108,C_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_311,plain,(
    ! [A_109,A_110] :
      ( r1_xboole_0(A_109,A_110)
      | ~ r1_tarski(A_109,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_291])).

tff(c_318,plain,(
    ! [A_110,A_109] :
      ( r1_xboole_0(A_110,A_109)
      | ~ r1_tarski(A_109,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_311,c_6])).

tff(c_121,plain,(
    ! [A_91,B_92] :
      ( k3_xboole_0(A_91,B_92) = A_91
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_134,plain,(
    k3_xboole_0('#skF_7','#skF_4') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_119,c_121])).

tff(c_457,plain,(
    ! [A_126,B_127,C_128] :
      ( ~ r1_xboole_0(A_126,B_127)
      | ~ r2_hidden(C_128,k3_xboole_0(A_126,B_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_466,plain,(
    ! [C_128] :
      ( ~ r1_xboole_0('#skF_7','#skF_4')
      | ~ r2_hidden(C_128,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_457])).

tff(c_568,plain,(
    ~ r1_xboole_0('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_466])).

tff(c_581,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_318,c_568])).

tff(c_1017,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_581])).

tff(c_1034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1017])).

tff(c_1036,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_959])).

tff(c_1108,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k5_mcart_1(A_170,B_171,C_172,D_173) = k1_mcart_1(k1_mcart_1(D_173))
      | ~ m1_subset_1(D_173,k3_zfmisc_1(A_170,B_171,C_172))
      | k1_xboole_0 = C_172
      | k1_xboole_0 = B_171
      | k1_xboole_0 = A_170 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1111,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_1108])).

tff(c_1114,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1036,c_1111])).

tff(c_1765,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1114])).

tff(c_62,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_118,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_103])).

tff(c_135,plain,(
    k3_xboole_0('#skF_8','#skF_5') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_118,c_121])).

tff(c_460,plain,(
    ! [C_128] :
      ( ~ r1_xboole_0('#skF_8','#skF_5')
      | ~ r2_hidden(C_128,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_457])).

tff(c_522,plain,(
    ~ r1_xboole_0('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_564,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_318,c_522])).

tff(c_1797,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1765,c_564])).

tff(c_1811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1797])).

tff(c_1813,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1114])).

tff(c_1252,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k6_mcart_1(A_184,B_185,C_186,D_187) = k2_mcart_1(k1_mcart_1(D_187))
      | ~ m1_subset_1(D_187,k3_zfmisc_1(A_184,B_185,C_186))
      | k1_xboole_0 = C_186
      | k1_xboole_0 = B_185
      | k1_xboole_0 = A_184 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1255,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_1252])).

tff(c_1258,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1036,c_1255])).

tff(c_1876,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_1813,c_1258])).

tff(c_1877,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1876])).

tff(c_60,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_117,plain,(
    r1_tarski('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_103])).

tff(c_136,plain,(
    k3_xboole_0('#skF_9','#skF_6') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_117,c_121])).

tff(c_463,plain,(
    ! [C_128] :
      ( ~ r1_xboole_0('#skF_9','#skF_6')
      | ~ r2_hidden(C_128,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_457])).

tff(c_594,plain,(
    ~ r1_xboole_0('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_607,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_318,c_594])).

tff(c_1910,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1877,c_607])).

tff(c_1928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1910])).

tff(c_1930,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1876])).

tff(c_1812,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_1114])).

tff(c_2310,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_1930,c_1812])).

tff(c_56,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_671,plain,(
    ! [A_145,B_146,C_147] : k2_zfmisc_1(k2_zfmisc_1(A_145,B_146),C_147) = k3_zfmisc_1(A_145,B_146,C_147) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden(k1_mcart_1(A_32),B_33)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_33,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4355,plain,(
    ! [A_301,A_302,B_303,C_304] :
      ( r2_hidden(k1_mcart_1(A_301),k2_zfmisc_1(A_302,B_303))
      | ~ r2_hidden(A_301,k3_zfmisc_1(A_302,B_303,C_304)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_42])).

tff(c_4399,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_56,c_4355])).

tff(c_4405,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_4399,c_42])).

tff(c_4422,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2310,c_4405])).

tff(c_4424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_4422])).

tff(c_4425,plain,(
    ! [C_128] : ~ r2_hidden(C_128,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_4484,plain,(
    ! [A_306,B_307,C_308] : k2_zfmisc_1(k2_zfmisc_1(A_306,B_307),C_308) = k3_zfmisc_1(A_306,B_307,C_308) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    ! [A_32,C_34,B_33] :
      ( r2_hidden(k2_mcart_1(A_32),C_34)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_33,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5627,plain,(
    ! [A_375,C_376,A_377,B_378] :
      ( r2_hidden(k2_mcart_1(A_375),C_376)
      | ~ r2_hidden(A_375,k3_zfmisc_1(A_377,B_378,C_376)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4484,c_40])).

tff(c_5635,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_5627])).

tff(c_5641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4425,c_5635])).

tff(c_5642,plain,(
    ! [C_128] : ~ r2_hidden(C_128,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_7779,plain,(
    ! [C_501] : v1_xboole_0(k2_zfmisc_1('#skF_7',C_501)) ),
    inference(resolution,[status(thm)],[c_7730,c_5642])).

tff(c_5644,plain,(
    ! [C_379] : ~ r2_hidden(C_379,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_466])).

tff(c_5654,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_52,c_5644])).

tff(c_91,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_3'(A_84),A_84)
      | k1_xboole_0 = A_84 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_84] :
      ( ~ v1_xboole_0(A_84)
      | k1_xboole_0 = A_84 ) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_5668,plain,(
    ! [A_84] :
      ( ~ v1_xboole_0(A_84)
      | A_84 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5654,c_95])).

tff(c_7786,plain,(
    ! [C_501] : k2_zfmisc_1('#skF_7',C_501) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_7779,c_5668])).

tff(c_7790,plain,(
    ! [C_502] : k2_zfmisc_1('#skF_7',C_502) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_7779,c_5668])).

tff(c_38,plain,(
    ! [A_29,B_30,C_31] : k2_zfmisc_1(k2_zfmisc_1(A_29,B_30),C_31) = k3_zfmisc_1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7811,plain,(
    ! [C_502,C_31] : k3_zfmisc_1('#skF_7',C_502,C_31) = k2_zfmisc_1('#skF_7',C_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_7790,c_38])).

tff(c_7824,plain,(
    ! [C_502,C_31] : k3_zfmisc_1('#skF_7',C_502,C_31) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7786,c_7811])).

tff(c_28,plain,(
    ! [A_23,B_24] : r1_xboole_0(k4_xboole_0(A_23,B_24),B_24) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_75,plain,(
    ! [B_24,A_23] : r1_xboole_0(B_24,k4_xboole_0(A_23,B_24)) ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_180,plain,(
    ! [B_24,A_23] : k4_xboole_0(B_24,k4_xboole_0(A_23,B_24)) = B_24 ),
    inference(resolution,[status(thm)],[c_75,c_163])).

tff(c_333,plain,(
    ! [A_115,B_116,C_117] :
      ( r1_tarski(A_115,B_116)
      | ~ r1_tarski(A_115,k4_xboole_0(B_116,C_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_348,plain,(
    ! [B_118,C_119] : r1_tarski(k4_xboole_0(B_118,C_119),B_118) ),
    inference(resolution,[status(thm)],[c_16,c_333])).

tff(c_18,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_xboole_0(A_14,C_16)
      | ~ r1_tarski(A_14,k4_xboole_0(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_428,plain,(
    ! [B_123,C_124,C_125] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_123,C_124),C_125),C_124) ),
    inference(resolution,[status(thm)],[c_348,c_18])).

tff(c_6472,plain,(
    ! [B_433,C_434,A_435] : r1_xboole_0(k4_xboole_0(B_433,C_434),k4_xboole_0(A_435,B_433)) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_428])).

tff(c_137,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_16,c_121])).

tff(c_6343,plain,(
    ! [A_426,B_427] :
      ( ~ r1_xboole_0(A_426,B_427)
      | v1_xboole_0(k3_xboole_0(A_426,B_427)) ) ),
    inference(resolution,[status(thm)],[c_4,c_457])).

tff(c_6372,plain,(
    ! [B_13] :
      ( ~ r1_xboole_0(B_13,B_13)
      | v1_xboole_0(B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_6343])).

tff(c_6520,plain,(
    ! [A_436] : v1_xboole_0(k4_xboole_0(A_436,A_436)) ),
    inference(resolution,[status(thm)],[c_6472,c_6372])).

tff(c_6534,plain,(
    ! [A_436] : k4_xboole_0(A_436,A_436) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6520,c_5668])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k4_xboole_0(A_25,B_26) != A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6386,plain,(
    ! [B_428] :
      ( ~ r1_xboole_0(B_428,B_428)
      | v1_xboole_0(B_428) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_6343])).

tff(c_6422,plain,(
    ! [B_26] :
      ( v1_xboole_0(B_26)
      | k4_xboole_0(B_26,B_26) != B_26 ) ),
    inference(resolution,[status(thm)],[c_32,c_6386])).

tff(c_6712,plain,(
    ! [B_443] :
      ( v1_xboole_0(B_443)
      | B_443 != '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6534,c_6422])).

tff(c_85,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_6732,plain,(
    k3_zfmisc_1('#skF_7','#skF_8','#skF_9') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_6712,c_85])).

tff(c_7909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7824,c_6732])).

tff(c_7910,plain,(
    ! [C_128] : ~ r2_hidden(C_128,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_8027,plain,(
    ! [A_512,C_513,B_514] :
      ( r2_hidden(k2_mcart_1(A_512),C_513)
      | ~ r2_hidden(A_512,k2_zfmisc_1(B_514,C_513)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_9712,plain,(
    ! [B_617,C_618] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_617,C_618))),C_618)
      | v1_xboole_0(k2_zfmisc_1(B_617,C_618)) ) ),
    inference(resolution,[status(thm)],[c_4,c_8027])).

tff(c_9755,plain,(
    ! [B_619] : v1_xboole_0(k2_zfmisc_1(B_619,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_9712,c_7910])).

tff(c_7912,plain,(
    ! [C_506] : ~ r2_hidden(C_506,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_7922,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_52,c_7912])).

tff(c_7963,plain,(
    ! [A_84] :
      ( ~ v1_xboole_0(A_84)
      | A_84 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7922,c_95])).

tff(c_9763,plain,(
    ! [B_619] : k2_zfmisc_1(B_619,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_9755,c_7963])).

tff(c_8240,plain,(
    ! [A_525,B_526,C_527] : k2_zfmisc_1(k2_zfmisc_1(A_525,B_526),C_527) = k3_zfmisc_1(A_525,B_526,C_527) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10273,plain,(
    ! [A_642,A_643,B_644,C_645] :
      ( r2_hidden(k1_mcart_1(A_642),k2_zfmisc_1(A_643,B_644))
      | ~ r2_hidden(A_642,k3_zfmisc_1(A_643,B_644,C_645)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8240,c_42])).

tff(c_10291,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_56,c_10273])).

tff(c_10299,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9763,c_10291])).

tff(c_10301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7910,c_10299])).

tff(c_10302,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8')
    | ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_10446,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_10302])).

tff(c_11658,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11657,c_10446])).

tff(c_10837,plain,(
    ! [A_696,C_697,B_698] :
      ( r2_hidden(k2_mcart_1(A_696),C_697)
      | ~ r2_hidden(A_696,k2_zfmisc_1(B_698,C_697)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12239,plain,(
    ! [A_780,C_781,A_782,B_783] :
      ( r2_hidden(k2_mcart_1(A_780),C_781)
      | ~ r2_hidden(A_780,k3_zfmisc_1(A_782,B_783,C_781)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_10837])).

tff(c_12247,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_12239])).

tff(c_12253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11658,c_12247])).

tff(c_12254,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_11215])).

tff(c_12256,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_12254])).

tff(c_10318,plain,(
    k3_xboole_0('#skF_8','#skF_5') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_118,c_10304])).

tff(c_10536,plain,(
    ! [C_674] :
      ( ~ r1_xboole_0('#skF_8','#skF_5')
      | ~ r2_hidden(C_674,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10318,c_10527])).

tff(c_10665,plain,(
    ~ r1_xboole_0('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_10536])).

tff(c_10694,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10506,c_10665])).

tff(c_12280,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12256,c_10694])).

tff(c_12299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12280])).

tff(c_12301,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12254])).

tff(c_11216,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11111])).

tff(c_11340,plain,(
    ! [A_729,B_730,C_731,D_732] :
      ( k5_mcart_1(A_729,B_730,C_731,D_732) = k1_mcart_1(k1_mcart_1(D_732))
      | ~ m1_subset_1(D_732,k3_zfmisc_1(A_729,B_730,C_731))
      | k1_xboole_0 = C_731
      | k1_xboole_0 = B_730
      | k1_xboole_0 = A_729 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_11343,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_11340])).

tff(c_11346,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_11216,c_11343])).

tff(c_12302,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_12301,c_11346])).

tff(c_12303,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_12302])).

tff(c_10319,plain,(
    k3_xboole_0('#skF_9','#skF_6') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_117,c_10304])).

tff(c_10530,plain,(
    ! [C_674] :
      ( ~ r1_xboole_0('#skF_9','#skF_6')
      | ~ r2_hidden(C_674,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10319,c_10527])).

tff(c_10664,plain,(
    ~ r1_xboole_0('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_10530])).

tff(c_10678,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10506,c_10664])).

tff(c_12329,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12303,c_10678])).

tff(c_12347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_12329])).

tff(c_12349,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12302])).

tff(c_12300,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12254])).

tff(c_12350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12349,c_12300])).

tff(c_12369,plain,(
    ! [C_784] : ~ r2_hidden(C_784,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_10536])).

tff(c_12379,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_52,c_12369])).

tff(c_10362,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(resolution,[status(thm)],[c_26,c_10346])).

tff(c_12419,plain,(
    ! [A_22] : k4_xboole_0(A_22,'#skF_8') = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12379,c_10362])).

tff(c_44,plain,(
    ! [A_35,B_36,C_37,D_39] :
      ( k7_mcart_1(A_35,B_36,C_37,D_39) = k2_mcart_1(D_39)
      | ~ m1_subset_1(D_39,k3_zfmisc_1(A_35,B_36,C_37))
      | k1_xboole_0 = C_37
      | k1_xboole_0 = B_36
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_12909,plain,(
    ! [A_822,B_823,C_824,D_825] :
      ( k7_mcart_1(A_822,B_823,C_824,D_825) = k2_mcart_1(D_825)
      | ~ m1_subset_1(D_825,k3_zfmisc_1(A_822,B_823,C_824))
      | C_824 = '#skF_8'
      | B_823 = '#skF_8'
      | A_822 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12379,c_12379,c_12379,c_44])).

tff(c_12913,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_8'
    | '#skF_8' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_12909])).

tff(c_13036,plain,(
    '#skF_8' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_12913])).

tff(c_12410,plain,(
    ~ r1_tarski('#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12379,c_10605])).

tff(c_13051,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13036,c_12410])).

tff(c_13067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_13051])).

tff(c_13068,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_6' = '#skF_8'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_12913])).

tff(c_13405,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_13068])).

tff(c_13815,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13405,c_10446])).

tff(c_12605,plain,(
    ! [A_796,C_797,B_798] :
      ( r2_hidden(k2_mcart_1(A_796),C_797)
      | ~ r2_hidden(A_796,k2_zfmisc_1(B_798,C_797)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_14029,plain,(
    ! [A_891,C_892,A_893,B_894] :
      ( r2_hidden(k2_mcart_1(A_891),C_892)
      | ~ r2_hidden(A_891,k3_zfmisc_1(A_893,B_894,C_892)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_12605])).

tff(c_14037,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_14029])).

tff(c_14043,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13815,c_14037])).

tff(c_14044,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_13068])).

tff(c_14176,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_14044])).

tff(c_10463,plain,(
    ! [B_659,A_660] :
      ( B_659 = A_660
      | ~ r1_tarski(B_659,A_660)
      | ~ r1_tarski(A_660,B_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10473,plain,
    ( '#skF_5' = '#skF_8'
    | ~ r1_tarski('#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_118,c_10463])).

tff(c_10498,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_10473])).

tff(c_14177,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14176,c_10498])).

tff(c_14184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14177])).

tff(c_14185,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_14044])).

tff(c_12368,plain,(
    k4_xboole_0('#skF_9','#skF_6') != '#skF_9' ),
    inference(resolution,[status(thm)],[c_32,c_10664])).

tff(c_14198,plain,(
    k4_xboole_0('#skF_9','#skF_8') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14185,c_12368])).

tff(c_14211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12419,c_14198])).

tff(c_14212,plain,(
    ! [C_674] : ~ r2_hidden(C_674,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_10530])).

tff(c_14537,plain,(
    ! [A_927,B_928,C_929] : k2_zfmisc_1(k2_zfmisc_1(A_927,B_928),C_929) = k3_zfmisc_1(A_927,B_928,C_929) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_15820,plain,(
    ! [A_1007,C_1008,A_1009,B_1010] :
      ( r2_hidden(k2_mcart_1(A_1007),C_1008)
      | ~ r2_hidden(A_1007,k3_zfmisc_1(A_1009,B_1010,C_1008)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14537,c_40])).

tff(c_15828,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_15820])).

tff(c_15834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14212,c_15828])).

tff(c_15835,plain,(
    ! [C_674] : ~ r2_hidden(C_674,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_10533])).

tff(c_10303,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_15838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15835,c_10303])).

tff(c_15839,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_10473])).

tff(c_15845,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15839,c_58])).

tff(c_16773,plain,(
    ! [A_1075,B_1076,C_1077,D_1078] :
      ( k7_mcart_1(A_1075,B_1076,C_1077,D_1078) = k2_mcart_1(D_1078)
      | ~ m1_subset_1(D_1078,k3_zfmisc_1(A_1075,B_1076,C_1077))
      | k1_xboole_0 = C_1077
      | k1_xboole_0 = B_1076
      | k1_xboole_0 = A_1075 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16777,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15845,c_16773])).

tff(c_16830,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16777])).

tff(c_15859,plain,(
    ! [A_1011,A_1012] :
      ( r1_xboole_0(A_1011,A_1012)
      | ~ r1_tarski(A_1011,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10360,c_10480])).

tff(c_15866,plain,(
    ! [A_1012,A_1011] :
      ( r1_xboole_0(A_1012,A_1011)
      | ~ r1_tarski(A_1011,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_15859,c_6])).

tff(c_15875,plain,(
    ! [A_1015,B_1016,C_1017] :
      ( ~ r1_xboole_0(A_1015,B_1016)
      | ~ r2_hidden(C_1017,k3_xboole_0(A_1015,B_1016)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_15881,plain,(
    ! [C_1017] :
      ( ~ r1_xboole_0('#skF_7','#skF_4')
      | ~ r2_hidden(C_1017,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10317,c_15875])).

tff(c_15941,plain,(
    ~ r1_xboole_0('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_15881])).

tff(c_15954,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_15866,c_15941])).

tff(c_16851,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16830,c_15954])).

tff(c_16864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16851])).

tff(c_16865,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_16777])).

tff(c_17040,plain,(
    k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_16865])).

tff(c_15841,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15839,c_10446])).

tff(c_17041,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17040,c_15841])).

tff(c_16423,plain,(
    ! [A_1057,B_1058,C_1059] : k2_zfmisc_1(k2_zfmisc_1(A_1057,B_1058),C_1059) = k3_zfmisc_1(A_1057,B_1058,C_1059) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_17823,plain,(
    ! [A_1134,C_1135,A_1136,B_1137] :
      ( r2_hidden(k2_mcart_1(A_1134),C_1135)
      | ~ r2_hidden(A_1134,k3_zfmisc_1(A_1136,B_1137,C_1135)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16423,c_40])).

tff(c_17828,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_17823])).

tff(c_17833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17041,c_17828])).

tff(c_17834,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_16865])).

tff(c_17836,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_17834])).

tff(c_10320,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_16,c_10304])).

tff(c_15895,plain,(
    ! [B_1018,C_1019] :
      ( ~ r1_xboole_0(B_1018,B_1018)
      | ~ r2_hidden(C_1019,B_1018) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10320,c_15875])).

tff(c_15918,plain,(
    ! [C_1019] : ~ r2_hidden(C_1019,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_76,c_15895])).

tff(c_17863,plain,(
    ! [C_1019] : ~ r2_hidden(C_1019,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17836,c_15918])).

tff(c_10359,plain,(
    ! [B_24,A_23] : k4_xboole_0(B_24,k4_xboole_0(A_23,B_24)) = B_24 ),
    inference(resolution,[status(thm)],[c_75,c_10346])).

tff(c_15958,plain,(
    ! [A_1021,B_1022,C_1023] :
      ( r1_tarski(A_1021,B_1022)
      | ~ r1_tarski(A_1021,k4_xboole_0(B_1022,C_1023)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_15973,plain,(
    ! [B_1024,C_1025] : r1_tarski(k4_xboole_0(B_1024,C_1025),B_1024) ),
    inference(resolution,[status(thm)],[c_16,c_15958])).

tff(c_16335,plain,(
    ! [B_1051,C_1052,C_1053] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_1051,C_1052),C_1053),C_1052) ),
    inference(resolution,[status(thm)],[c_15973,c_18])).

tff(c_16505,plain,(
    ! [B_1066,C_1067,A_1068] : r1_xboole_0(k4_xboole_0(B_1066,C_1067),k4_xboole_0(A_1068,B_1066)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10359,c_16335])).

tff(c_16247,plain,(
    ! [A_1044,B_1045] :
      ( ~ r1_xboole_0(A_1044,B_1045)
      | v1_xboole_0(k3_xboole_0(A_1044,B_1045)) ) ),
    inference(resolution,[status(thm)],[c_4,c_15875])).

tff(c_16271,plain,(
    ! [B_13] :
      ( ~ r1_xboole_0(B_13,B_13)
      | v1_xboole_0(B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10320,c_16247])).

tff(c_16553,plain,(
    ! [A_1069] : v1_xboole_0(k4_xboole_0(A_1069,A_1069)) ),
    inference(resolution,[status(thm)],[c_16505,c_16271])).

tff(c_16564,plain,(
    ! [A_1069] : k4_xboole_0(A_1069,A_1069) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16553,c_95])).

tff(c_10447,plain,(
    ! [A_655,B_656] :
      ( r1_xboole_0(A_655,B_656)
      | k4_xboole_0(A_655,B_656) != A_655 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10454,plain,(
    ! [B_656,A_655] :
      ( r1_xboole_0(B_656,A_655)
      | k4_xboole_0(A_655,B_656) != A_655 ) ),
    inference(resolution,[status(thm)],[c_10447,c_6])).

tff(c_16291,plain,(
    ! [B_1049] :
      ( ~ r1_xboole_0(B_1049,B_1049)
      | v1_xboole_0(B_1049) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10320,c_16247])).

tff(c_16318,plain,(
    ! [A_655] :
      ( v1_xboole_0(A_655)
      | k4_xboole_0(A_655,A_655) != A_655 ) ),
    inference(resolution,[status(thm)],[c_10454,c_16291])).

tff(c_16572,plain,(
    ! [A_655] :
      ( v1_xboole_0(A_655)
      | k1_xboole_0 != A_655 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16564,c_16318])).

tff(c_17845,plain,(
    ! [A_655] :
      ( v1_xboole_0(A_655)
      | A_655 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17836,c_16572])).

tff(c_16205,plain,(
    ! [A_1039,C_1040,B_1041] :
      ( r2_hidden(k2_mcart_1(A_1039),C_1040)
      | ~ r2_hidden(A_1039,k2_zfmisc_1(B_1041,C_1040)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18824,plain,(
    ! [B_1185,C_1186] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1185,C_1186))),C_1186)
      | v1_xboole_0(k2_zfmisc_1(B_1185,C_1186)) ) ),
    inference(resolution,[status(thm)],[c_4,c_16205])).

tff(c_18950,plain,(
    ! [C_1194,B_1195] :
      ( ~ v1_xboole_0(C_1194)
      | v1_xboole_0(k2_zfmisc_1(B_1195,C_1194)) ) ),
    inference(resolution,[status(thm)],[c_18824,c_2])).

tff(c_17868,plain,(
    ! [A_84] :
      ( ~ v1_xboole_0(A_84)
      | A_84 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17836,c_95])).

tff(c_18963,plain,(
    ! [B_1196,C_1197] :
      ( k2_zfmisc_1(B_1196,C_1197) = '#skF_8'
      | ~ v1_xboole_0(C_1197) ) ),
    inference(resolution,[status(thm)],[c_18950,c_17868])).

tff(c_19178,plain,(
    ! [B_1196] : k2_zfmisc_1(B_1196,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_17845,c_18963])).

tff(c_20402,plain,(
    ! [A_1254,A_1255,B_1256,C_1257] :
      ( r2_hidden(k1_mcart_1(A_1254),k2_zfmisc_1(A_1255,B_1256))
      | ~ r2_hidden(A_1254,k3_zfmisc_1(A_1255,B_1256,C_1257)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16423,c_42])).

tff(c_20428,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_56,c_20402])).

tff(c_20439,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19178,c_20428])).

tff(c_20441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17863,c_20439])).

tff(c_20442,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_17834])).

tff(c_15878,plain,(
    ! [C_1017] :
      ( ~ r1_xboole_0('#skF_9','#skF_6')
      | ~ r2_hidden(C_1017,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10319,c_15875])).

tff(c_16003,plain,(
    ~ r1_xboole_0('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_15878])).

tff(c_16016,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_15866,c_16003])).

tff(c_20467,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20442,c_16016])).

tff(c_20482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20467])).

tff(c_20483,plain,(
    ! [C_1017] : ~ r2_hidden(C_1017,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_15878])).

tff(c_20885,plain,(
    ! [A_1286,C_1287,B_1288] :
      ( r2_hidden(k2_mcart_1(A_1286),C_1287)
      | ~ r2_hidden(A_1286,k2_zfmisc_1(B_1288,C_1287)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22702,plain,(
    ! [A_1386,C_1387,A_1388,B_1389] :
      ( r2_hidden(k2_mcart_1(A_1386),C_1387)
      | ~ r2_hidden(A_1386,k3_zfmisc_1(A_1388,B_1389,C_1387)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_20885])).

tff(c_22713,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_22702])).

tff(c_22720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20483,c_22713])).

tff(c_22721,plain,(
    ! [C_1017] : ~ r2_hidden(C_1017,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_15881])).

tff(c_15843,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15839,c_10303])).

tff(c_22724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22721,c_15843])).

tff(c_22725,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_10302])).

tff(c_23489,plain,(
    ! [A_1450,B_1451,C_1452,D_1453] :
      ( k7_mcart_1(A_1450,B_1451,C_1452,D_1453) = k2_mcart_1(D_1453)
      | ~ m1_subset_1(D_1453,k3_zfmisc_1(A_1450,B_1451,C_1452))
      | k1_xboole_0 = C_1452
      | k1_xboole_0 = B_1451
      | k1_xboole_0 = A_1450 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_23493,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_23489])).

tff(c_23566,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_23493])).

tff(c_22943,plain,(
    ! [A_1413,C_1414,B_1415] :
      ( r1_xboole_0(A_1413,C_1414)
      | ~ r1_xboole_0(B_1415,C_1414)
      | ~ r1_tarski(A_1413,B_1415) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22963,plain,(
    ! [A_1416,A_1417] :
      ( r1_xboole_0(A_1416,A_1417)
      | ~ r1_tarski(A_1416,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_76,c_22943])).

tff(c_23014,plain,(
    ! [A_1421,A_1422] :
      ( r1_xboole_0(A_1421,A_1422)
      | ~ r1_tarski(A_1422,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22963,c_6])).

tff(c_22841,plain,(
    ! [A_1404,B_1405,C_1406] :
      ( ~ r1_xboole_0(A_1404,B_1405)
      | ~ r2_hidden(C_1406,k3_xboole_0(A_1404,B_1405)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22847,plain,(
    ! [C_1406] :
      ( ~ r1_xboole_0('#skF_7','#skF_4')
      | ~ r2_hidden(C_1406,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10317,c_22841])).

tff(c_22986,plain,(
    ~ r1_xboole_0('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22847])).

tff(c_23034,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_23014,c_22986])).

tff(c_23579,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23566,c_23034])).

tff(c_23595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_23579])).

tff(c_23597,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_23493])).

tff(c_23786,plain,(
    ! [A_1472,B_1473,C_1474,D_1475] :
      ( k5_mcart_1(A_1472,B_1473,C_1474,D_1475) = k1_mcart_1(k1_mcart_1(D_1475))
      | ~ m1_subset_1(D_1475,k3_zfmisc_1(A_1472,B_1473,C_1474))
      | k1_xboole_0 = C_1474
      | k1_xboole_0 = B_1473
      | k1_xboole_0 = A_1472 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_23789,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_23786])).

tff(c_23792,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_23597,c_23789])).

tff(c_24270,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_23792])).

tff(c_22850,plain,(
    ! [C_1406] :
      ( ~ r1_xboole_0('#skF_8','#skF_5')
      | ~ r2_hidden(C_1406,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10318,c_22841])).

tff(c_22926,plain,(
    ~ r1_xboole_0('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_22850])).

tff(c_23036,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_23014,c_22926])).

tff(c_24300,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24270,c_23036])).

tff(c_24316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24300])).

tff(c_24318,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_23792])).

tff(c_22747,plain,(
    ! [A_1394,B_1395,C_1396] :
      ( r1_tarski(A_1394,B_1395)
      | ~ r1_tarski(A_1394,k4_xboole_0(B_1395,C_1396)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22761,plain,(
    ! [B_1395,C_1396] : r1_tarski(k4_xboole_0(B_1395,C_1396),B_1395) ),
    inference(resolution,[status(thm)],[c_16,c_22747])).

tff(c_22893,plain,(
    ! [A_1410,C_1411,B_1412] :
      ( r1_xboole_0(A_1410,C_1411)
      | ~ r1_tarski(A_1410,k4_xboole_0(B_1412,C_1411)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_23502,plain,(
    ! [B_1455,C_1456,C_1457] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_1455,C_1456),C_1457),C_1456) ),
    inference(resolution,[status(thm)],[c_22761,c_22893])).

tff(c_23634,plain,(
    ! [B_1467,C_1468,A_1469] : r1_xboole_0(k4_xboole_0(B_1467,C_1468),k4_xboole_0(A_1469,B_1467)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10359,c_23502])).

tff(c_23271,plain,(
    ! [A_1441,B_1442] :
      ( ~ r1_xboole_0(A_1441,B_1442)
      | v1_xboole_0(k3_xboole_0(A_1441,B_1442)) ) ),
    inference(resolution,[status(thm)],[c_4,c_22841])).

tff(c_23298,plain,(
    ! [B_13] :
      ( ~ r1_xboole_0(B_13,B_13)
      | v1_xboole_0(B_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10320,c_23271])).

tff(c_23682,plain,(
    ! [A_1470] : v1_xboole_0(k4_xboole_0(A_1470,A_1470)) ),
    inference(resolution,[status(thm)],[c_23634,c_23298])).

tff(c_23696,plain,(
    ! [A_1470] : k4_xboole_0(A_1470,A_1470) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_23682,c_95])).

tff(c_24357,plain,(
    ! [A_1506,B_1507,A_1508] :
      ( r1_xboole_0(A_1506,B_1507)
      | ~ r1_tarski(A_1506,A_1508)
      | k4_xboole_0(A_1508,B_1507) != A_1508 ) ),
    inference(resolution,[status(thm)],[c_32,c_22943])).

tff(c_24440,plain,(
    ! [B_1511] :
      ( r1_xboole_0('#skF_9',B_1511)
      | k4_xboole_0('#skF_6',B_1511) != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_117,c_24357])).

tff(c_22844,plain,(
    ! [C_1406] :
      ( ~ r1_xboole_0('#skF_9','#skF_6')
      | ~ r2_hidden(C_1406,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10319,c_22841])).

tff(c_22925,plain,(
    ~ r1_xboole_0('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_22844])).

tff(c_24452,plain,(
    k4_xboole_0('#skF_6','#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_24440,c_22925])).

tff(c_24466,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23696,c_24452])).

tff(c_23598,plain,(
    ! [A_1460,B_1461,C_1462,D_1463] :
      ( k6_mcart_1(A_1460,B_1461,C_1462,D_1463) = k2_mcart_1(k1_mcart_1(D_1463))
      | ~ m1_subset_1(D_1463,k3_zfmisc_1(A_1460,B_1461,C_1462))
      | k1_xboole_0 = C_1462
      | k1_xboole_0 = B_1461
      | k1_xboole_0 = A_1460 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_23601,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_23598])).

tff(c_23604,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_23597,c_23601])).

tff(c_24648,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_24318,c_24466,c_23604])).

tff(c_23100,plain,(
    ! [A_1427,B_1428,C_1429] :
      ( r2_hidden(k1_mcart_1(A_1427),B_1428)
      | ~ r2_hidden(A_1427,k2_zfmisc_1(B_1428,C_1429)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_27039,plain,(
    ! [A_1605,A_1606,B_1607,C_1608] :
      ( r2_hidden(k1_mcart_1(A_1605),k2_zfmisc_1(A_1606,B_1607))
      | ~ r2_hidden(A_1605,k3_zfmisc_1(A_1606,B_1607,C_1608)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_23100])).

tff(c_27079,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_56,c_27039])).

tff(c_27084,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_27079,c_40])).

tff(c_27101,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24648,c_27084])).

tff(c_27103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22725,c_27101])).

tff(c_27104,plain,(
    ! [C_1406] : ~ r2_hidden(C_1406,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_22847])).

tff(c_27107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27104,c_10303])).

tff(c_27108,plain,(
    ! [C_1406] : ~ r2_hidden(C_1406,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_22850])).

tff(c_27289,plain,(
    ! [A_1617,C_1618,B_1619] :
      ( r2_hidden(k2_mcart_1(A_1617),C_1618)
      | ~ r2_hidden(A_1617,k2_zfmisc_1(B_1619,C_1618)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28839,plain,(
    ! [B_1720,C_1721] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1720,C_1721))),C_1721)
      | v1_xboole_0(k2_zfmisc_1(B_1720,C_1721)) ) ),
    inference(resolution,[status(thm)],[c_4,c_27289])).

tff(c_28882,plain,(
    ! [B_1722] : v1_xboole_0(k2_zfmisc_1(B_1722,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_28839,c_27108])).

tff(c_27119,plain,(
    ! [C_1609] : ~ r2_hidden(C_1609,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_22850])).

tff(c_27129,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_52,c_27119])).

tff(c_27138,plain,(
    ! [A_84] :
      ( ~ v1_xboole_0(A_84)
      | A_84 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27129,c_95])).

tff(c_28890,plain,(
    ! [B_1722] : k2_zfmisc_1(B_1722,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_28882,c_27138])).

tff(c_27442,plain,(
    ! [A_1629,B_1630,C_1631] :
      ( r2_hidden(k1_mcart_1(A_1629),B_1630)
      | ~ r2_hidden(A_1629,k2_zfmisc_1(B_1630,C_1631)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_29369,plain,(
    ! [A_1743,A_1744,B_1745,C_1746] :
      ( r2_hidden(k1_mcart_1(A_1743),k2_zfmisc_1(A_1744,B_1745))
      | ~ r2_hidden(A_1743,k3_zfmisc_1(A_1744,B_1745,C_1746)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_27442])).

tff(c_29387,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_56,c_29369])).

tff(c_29395,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28890,c_29387])).

tff(c_29397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27108,c_29395])).

tff(c_29398,plain,(
    ! [C_1406] : ~ r2_hidden(C_1406,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_22844])).

tff(c_22726,plain,(
    r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_10302])).

tff(c_29401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29398,c_22726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.62/3.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.08/3.94  
% 10.08/3.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.08/3.95  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_2
% 10.08/3.95  
% 10.08/3.95  %Foreground sorts:
% 10.08/3.95  
% 10.08/3.95  
% 10.08/3.95  %Background operators:
% 10.08/3.95  
% 10.08/3.95  
% 10.08/3.95  %Foreground operators:
% 10.08/3.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.08/3.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.08/3.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.08/3.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.08/3.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.08/3.95  tff('#skF_7', type, '#skF_7': $i).
% 10.08/3.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.08/3.95  tff('#skF_10', type, '#skF_10': $i).
% 10.08/3.95  tff('#skF_5', type, '#skF_5': $i).
% 10.08/3.95  tff('#skF_6', type, '#skF_6': $i).
% 10.08/3.95  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.08/3.95  tff('#skF_9', type, '#skF_9': $i).
% 10.08/3.95  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 10.08/3.95  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 10.08/3.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.08/3.95  tff('#skF_8', type, '#skF_8': $i).
% 10.08/3.95  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 10.08/3.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.08/3.95  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 10.08/3.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.08/3.95  tff('#skF_4', type, '#skF_4': $i).
% 10.08/3.95  tff('#skF_3', type, '#skF_3': $i > $i).
% 10.08/3.95  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 10.08/3.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.08/3.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.08/3.95  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 10.08/3.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.08/3.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.08/3.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.08/3.95  
% 10.08/3.98  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.08/3.98  tff(f_132, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 10.08/3.98  tff(f_152, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 10.08/3.98  tff(f_111, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 10.08/3.98  tff(f_73, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 10.08/3.98  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.08/3.98  tff(f_79, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.08/3.98  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 10.08/3.98  tff(f_83, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.08/3.98  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.08/3.98  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 10.08/3.98  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.08/3.98  tff(f_91, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 10.08/3.98  tff(f_85, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 10.08/3.98  tff(f_75, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 10.08/3.98  tff(f_71, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 10.08/3.98  tff(c_16, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.08/3.98  tff(c_52, plain, (![A_40]: (r2_hidden('#skF_3'(A_40), A_40) | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.08/3.98  tff(c_58, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.08/3.98  tff(c_11107, plain, (![A_713, B_714, C_715, D_716]: (k7_mcart_1(A_713, B_714, C_715, D_716)=k2_mcart_1(D_716) | ~m1_subset_1(D_716, k3_zfmisc_1(A_713, B_714, C_715)) | k1_xboole_0=C_715 | k1_xboole_0=B_714 | k1_xboole_0=A_713)), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.08/3.98  tff(c_11111, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_11107])).
% 10.08/3.98  tff(c_11183, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_11111])).
% 10.08/3.98  tff(c_26, plain, (![A_22]: (r1_xboole_0(A_22, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.08/3.98  tff(c_70, plain, (![B_79, A_80]: (r1_xboole_0(B_79, A_80) | ~r1_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.08/3.98  tff(c_76, plain, (![A_22]: (r1_xboole_0(k1_xboole_0, A_22))), inference(resolution, [status(thm)], [c_26, c_70])).
% 10.08/3.98  tff(c_10346, plain, (![A_649, B_650]: (k4_xboole_0(A_649, B_650)=A_649 | ~r1_xboole_0(A_649, B_650))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.08/3.98  tff(c_10360, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_76, c_10346])).
% 10.08/3.98  tff(c_10480, plain, (![A_661, C_662, B_663]: (r1_xboole_0(A_661, C_662) | ~r1_tarski(A_661, k4_xboole_0(B_663, C_662)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.08/3.98  tff(c_10499, plain, (![A_664, A_665]: (r1_xboole_0(A_664, A_665) | ~r1_tarski(A_664, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10360, c_10480])).
% 10.08/3.98  tff(c_6, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.08/3.98  tff(c_10506, plain, (![A_665, A_664]: (r1_xboole_0(A_665, A_664) | ~r1_tarski(A_664, k1_xboole_0))), inference(resolution, [status(thm)], [c_10499, c_6])).
% 10.08/3.98  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.08/3.98  tff(c_103, plain, (![A_89, B_90]: (r1_tarski(A_89, B_90) | ~m1_subset_1(A_89, k1_zfmisc_1(B_90)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.08/3.98  tff(c_119, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_103])).
% 10.08/3.98  tff(c_10304, plain, (![A_646, B_647]: (k3_xboole_0(A_646, B_647)=A_646 | ~r1_tarski(A_646, B_647))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.08/3.98  tff(c_10317, plain, (k3_xboole_0('#skF_7', '#skF_4')='#skF_7'), inference(resolution, [status(thm)], [c_119, c_10304])).
% 10.08/3.98  tff(c_10527, plain, (![A_672, B_673, C_674]: (~r1_xboole_0(A_672, B_673) | ~r2_hidden(C_674, k3_xboole_0(A_672, B_673)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.08/3.98  tff(c_10533, plain, (![C_674]: (~r1_xboole_0('#skF_7', '#skF_4') | ~r2_hidden(C_674, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10317, c_10527])).
% 10.08/3.98  tff(c_10592, plain, (~r1_xboole_0('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_10533])).
% 10.08/3.98  tff(c_10605, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_10506, c_10592])).
% 10.08/3.98  tff(c_11198, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11183, c_10605])).
% 10.08/3.98  tff(c_11214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_11198])).
% 10.08/3.98  tff(c_11215, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_11111])).
% 10.08/3.98  tff(c_11657, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_11215])).
% 10.08/3.98  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.08/3.98  tff(c_5793, plain, (![A_386, B_387, C_388]: (r2_hidden(k1_mcart_1(A_386), B_387) | ~r2_hidden(A_386, k2_zfmisc_1(B_387, C_388)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.08/3.98  tff(c_7730, plain, (![B_499, C_500]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_499, C_500))), B_499) | v1_xboole_0(k2_zfmisc_1(B_499, C_500)))), inference(resolution, [status(thm)], [c_4, c_5793])).
% 10.08/3.98  tff(c_54, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9') | ~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8') | ~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.08/3.98  tff(c_120, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 10.08/3.98  tff(c_955, plain, (![A_160, B_161, C_162, D_163]: (k7_mcart_1(A_160, B_161, C_162, D_163)=k2_mcart_1(D_163) | ~m1_subset_1(D_163, k3_zfmisc_1(A_160, B_161, C_162)) | k1_xboole_0=C_162 | k1_xboole_0=B_161 | k1_xboole_0=A_160)), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.08/3.98  tff(c_959, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_955])).
% 10.08/3.98  tff(c_1004, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_959])).
% 10.08/3.98  tff(c_163, plain, (![A_96, B_97]: (k4_xboole_0(A_96, B_97)=A_96 | ~r1_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.08/3.98  tff(c_181, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k1_xboole_0)), inference(resolution, [status(thm)], [c_76, c_163])).
% 10.08/3.98  tff(c_291, plain, (![A_106, C_107, B_108]: (r1_xboole_0(A_106, C_107) | ~r1_tarski(A_106, k4_xboole_0(B_108, C_107)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.08/3.98  tff(c_311, plain, (![A_109, A_110]: (r1_xboole_0(A_109, A_110) | ~r1_tarski(A_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_181, c_291])).
% 10.08/3.98  tff(c_318, plain, (![A_110, A_109]: (r1_xboole_0(A_110, A_109) | ~r1_tarski(A_109, k1_xboole_0))), inference(resolution, [status(thm)], [c_311, c_6])).
% 10.08/3.98  tff(c_121, plain, (![A_91, B_92]: (k3_xboole_0(A_91, B_92)=A_91 | ~r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.08/3.98  tff(c_134, plain, (k3_xboole_0('#skF_7', '#skF_4')='#skF_7'), inference(resolution, [status(thm)], [c_119, c_121])).
% 10.08/3.98  tff(c_457, plain, (![A_126, B_127, C_128]: (~r1_xboole_0(A_126, B_127) | ~r2_hidden(C_128, k3_xboole_0(A_126, B_127)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.08/3.98  tff(c_466, plain, (![C_128]: (~r1_xboole_0('#skF_7', '#skF_4') | ~r2_hidden(C_128, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_457])).
% 10.08/3.98  tff(c_568, plain, (~r1_xboole_0('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_466])).
% 10.08/3.98  tff(c_581, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_318, c_568])).
% 10.08/3.98  tff(c_1017, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_581])).
% 10.08/3.98  tff(c_1034, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_1017])).
% 10.08/3.98  tff(c_1036, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_959])).
% 10.08/3.98  tff(c_1108, plain, (![A_170, B_171, C_172, D_173]: (k5_mcart_1(A_170, B_171, C_172, D_173)=k1_mcart_1(k1_mcart_1(D_173)) | ~m1_subset_1(D_173, k3_zfmisc_1(A_170, B_171, C_172)) | k1_xboole_0=C_172 | k1_xboole_0=B_171 | k1_xboole_0=A_170)), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.08/3.98  tff(c_1111, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_1108])).
% 10.08/3.98  tff(c_1114, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1036, c_1111])).
% 10.08/3.98  tff(c_1765, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1114])).
% 10.08/3.98  tff(c_62, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.08/3.98  tff(c_118, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_103])).
% 10.08/3.98  tff(c_135, plain, (k3_xboole_0('#skF_8', '#skF_5')='#skF_8'), inference(resolution, [status(thm)], [c_118, c_121])).
% 10.08/3.98  tff(c_460, plain, (![C_128]: (~r1_xboole_0('#skF_8', '#skF_5') | ~r2_hidden(C_128, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_457])).
% 10.08/3.98  tff(c_522, plain, (~r1_xboole_0('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_460])).
% 10.08/3.99  tff(c_564, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_318, c_522])).
% 10.08/3.99  tff(c_1797, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1765, c_564])).
% 10.08/3.99  tff(c_1811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_1797])).
% 10.08/3.99  tff(c_1813, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_1114])).
% 10.08/3.99  tff(c_1252, plain, (![A_184, B_185, C_186, D_187]: (k6_mcart_1(A_184, B_185, C_186, D_187)=k2_mcart_1(k1_mcart_1(D_187)) | ~m1_subset_1(D_187, k3_zfmisc_1(A_184, B_185, C_186)) | k1_xboole_0=C_186 | k1_xboole_0=B_185 | k1_xboole_0=A_184)), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.08/3.99  tff(c_1255, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_1252])).
% 10.08/3.99  tff(c_1258, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1036, c_1255])).
% 10.08/3.99  tff(c_1876, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_1813, c_1258])).
% 10.08/3.99  tff(c_1877, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_1876])).
% 10.08/3.99  tff(c_60, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.08/3.99  tff(c_117, plain, (r1_tarski('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_103])).
% 10.08/3.99  tff(c_136, plain, (k3_xboole_0('#skF_9', '#skF_6')='#skF_9'), inference(resolution, [status(thm)], [c_117, c_121])).
% 10.08/3.99  tff(c_463, plain, (![C_128]: (~r1_xboole_0('#skF_9', '#skF_6') | ~r2_hidden(C_128, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_457])).
% 10.08/3.99  tff(c_594, plain, (~r1_xboole_0('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_463])).
% 10.08/3.99  tff(c_607, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_318, c_594])).
% 10.08/3.99  tff(c_1910, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1877, c_607])).
% 10.08/3.99  tff(c_1928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_1910])).
% 10.08/3.99  tff(c_1930, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_1876])).
% 10.08/3.99  tff(c_1812, plain, (k1_xboole_0='#skF_6' | k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_1114])).
% 10.08/3.99  tff(c_2310, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_1930, c_1812])).
% 10.08/3.99  tff(c_56, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 10.08/3.99  tff(c_671, plain, (![A_145, B_146, C_147]: (k2_zfmisc_1(k2_zfmisc_1(A_145, B_146), C_147)=k3_zfmisc_1(A_145, B_146, C_147))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.08/3.99  tff(c_42, plain, (![A_32, B_33, C_34]: (r2_hidden(k1_mcart_1(A_32), B_33) | ~r2_hidden(A_32, k2_zfmisc_1(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.08/3.99  tff(c_4355, plain, (![A_301, A_302, B_303, C_304]: (r2_hidden(k1_mcart_1(A_301), k2_zfmisc_1(A_302, B_303)) | ~r2_hidden(A_301, k3_zfmisc_1(A_302, B_303, C_304)))), inference(superposition, [status(thm), theory('equality')], [c_671, c_42])).
% 10.08/3.99  tff(c_4399, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_56, c_4355])).
% 10.08/3.99  tff(c_4405, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_7')), inference(resolution, [status(thm)], [c_4399, c_42])).
% 10.08/3.99  tff(c_4422, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2310, c_4405])).
% 10.08/3.99  tff(c_4424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_4422])).
% 10.08/3.99  tff(c_4425, plain, (![C_128]: (~r2_hidden(C_128, '#skF_9'))), inference(splitRight, [status(thm)], [c_463])).
% 10.08/3.99  tff(c_4484, plain, (![A_306, B_307, C_308]: (k2_zfmisc_1(k2_zfmisc_1(A_306, B_307), C_308)=k3_zfmisc_1(A_306, B_307, C_308))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.08/3.99  tff(c_40, plain, (![A_32, C_34, B_33]: (r2_hidden(k2_mcart_1(A_32), C_34) | ~r2_hidden(A_32, k2_zfmisc_1(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.08/3.99  tff(c_5627, plain, (![A_375, C_376, A_377, B_378]: (r2_hidden(k2_mcart_1(A_375), C_376) | ~r2_hidden(A_375, k3_zfmisc_1(A_377, B_378, C_376)))), inference(superposition, [status(thm), theory('equality')], [c_4484, c_40])).
% 10.08/3.99  tff(c_5635, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_56, c_5627])).
% 10.08/3.99  tff(c_5641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4425, c_5635])).
% 10.08/3.99  tff(c_5642, plain, (![C_128]: (~r2_hidden(C_128, '#skF_7'))), inference(splitRight, [status(thm)], [c_466])).
% 10.08/3.99  tff(c_7779, plain, (![C_501]: (v1_xboole_0(k2_zfmisc_1('#skF_7', C_501)))), inference(resolution, [status(thm)], [c_7730, c_5642])).
% 10.08/3.99  tff(c_5644, plain, (![C_379]: (~r2_hidden(C_379, '#skF_7'))), inference(splitRight, [status(thm)], [c_466])).
% 10.08/3.99  tff(c_5654, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_52, c_5644])).
% 10.08/3.99  tff(c_91, plain, (![A_84]: (r2_hidden('#skF_3'(A_84), A_84) | k1_xboole_0=A_84)), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.08/3.99  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.08/3.99  tff(c_95, plain, (![A_84]: (~v1_xboole_0(A_84) | k1_xboole_0=A_84)), inference(resolution, [status(thm)], [c_91, c_2])).
% 10.08/3.99  tff(c_5668, plain, (![A_84]: (~v1_xboole_0(A_84) | A_84='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5654, c_95])).
% 10.08/3.99  tff(c_7786, plain, (![C_501]: (k2_zfmisc_1('#skF_7', C_501)='#skF_7')), inference(resolution, [status(thm)], [c_7779, c_5668])).
% 10.08/3.99  tff(c_7790, plain, (![C_502]: (k2_zfmisc_1('#skF_7', C_502)='#skF_7')), inference(resolution, [status(thm)], [c_7779, c_5668])).
% 10.08/3.99  tff(c_38, plain, (![A_29, B_30, C_31]: (k2_zfmisc_1(k2_zfmisc_1(A_29, B_30), C_31)=k3_zfmisc_1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.08/3.99  tff(c_7811, plain, (![C_502, C_31]: (k3_zfmisc_1('#skF_7', C_502, C_31)=k2_zfmisc_1('#skF_7', C_31))), inference(superposition, [status(thm), theory('equality')], [c_7790, c_38])).
% 10.08/3.99  tff(c_7824, plain, (![C_502, C_31]: (k3_zfmisc_1('#skF_7', C_502, C_31)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7786, c_7811])).
% 10.08/3.99  tff(c_28, plain, (![A_23, B_24]: (r1_xboole_0(k4_xboole_0(A_23, B_24), B_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.08/3.99  tff(c_75, plain, (![B_24, A_23]: (r1_xboole_0(B_24, k4_xboole_0(A_23, B_24)))), inference(resolution, [status(thm)], [c_28, c_70])).
% 10.08/3.99  tff(c_180, plain, (![B_24, A_23]: (k4_xboole_0(B_24, k4_xboole_0(A_23, B_24))=B_24)), inference(resolution, [status(thm)], [c_75, c_163])).
% 10.08/3.99  tff(c_333, plain, (![A_115, B_116, C_117]: (r1_tarski(A_115, B_116) | ~r1_tarski(A_115, k4_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.08/3.99  tff(c_348, plain, (![B_118, C_119]: (r1_tarski(k4_xboole_0(B_118, C_119), B_118))), inference(resolution, [status(thm)], [c_16, c_333])).
% 10.08/3.99  tff(c_18, plain, (![A_14, C_16, B_15]: (r1_xboole_0(A_14, C_16) | ~r1_tarski(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.08/3.99  tff(c_428, plain, (![B_123, C_124, C_125]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_123, C_124), C_125), C_124))), inference(resolution, [status(thm)], [c_348, c_18])).
% 10.08/3.99  tff(c_6472, plain, (![B_433, C_434, A_435]: (r1_xboole_0(k4_xboole_0(B_433, C_434), k4_xboole_0(A_435, B_433)))), inference(superposition, [status(thm), theory('equality')], [c_180, c_428])).
% 10.08/3.99  tff(c_137, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_16, c_121])).
% 10.08/3.99  tff(c_6343, plain, (![A_426, B_427]: (~r1_xboole_0(A_426, B_427) | v1_xboole_0(k3_xboole_0(A_426, B_427)))), inference(resolution, [status(thm)], [c_4, c_457])).
% 10.08/3.99  tff(c_6372, plain, (![B_13]: (~r1_xboole_0(B_13, B_13) | v1_xboole_0(B_13))), inference(superposition, [status(thm), theory('equality')], [c_137, c_6343])).
% 10.08/3.99  tff(c_6520, plain, (![A_436]: (v1_xboole_0(k4_xboole_0(A_436, A_436)))), inference(resolution, [status(thm)], [c_6472, c_6372])).
% 10.08/3.99  tff(c_6534, plain, (![A_436]: (k4_xboole_0(A_436, A_436)='#skF_7')), inference(resolution, [status(thm)], [c_6520, c_5668])).
% 10.08/3.99  tff(c_32, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k4_xboole_0(A_25, B_26)!=A_25)), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.08/3.99  tff(c_6386, plain, (![B_428]: (~r1_xboole_0(B_428, B_428) | v1_xboole_0(B_428))), inference(superposition, [status(thm), theory('equality')], [c_137, c_6343])).
% 10.08/3.99  tff(c_6422, plain, (![B_26]: (v1_xboole_0(B_26) | k4_xboole_0(B_26, B_26)!=B_26)), inference(resolution, [status(thm)], [c_32, c_6386])).
% 10.08/3.99  tff(c_6712, plain, (![B_443]: (v1_xboole_0(B_443) | B_443!='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6534, c_6422])).
% 10.08/3.99  tff(c_85, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_56, c_2])).
% 10.08/3.99  tff(c_6732, plain, (k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')!='#skF_7'), inference(resolution, [status(thm)], [c_6712, c_85])).
% 10.08/3.99  tff(c_7909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7824, c_6732])).
% 10.08/3.99  tff(c_7910, plain, (![C_128]: (~r2_hidden(C_128, '#skF_8'))), inference(splitRight, [status(thm)], [c_460])).
% 10.08/3.99  tff(c_8027, plain, (![A_512, C_513, B_514]: (r2_hidden(k2_mcart_1(A_512), C_513) | ~r2_hidden(A_512, k2_zfmisc_1(B_514, C_513)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.08/3.99  tff(c_9712, plain, (![B_617, C_618]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_617, C_618))), C_618) | v1_xboole_0(k2_zfmisc_1(B_617, C_618)))), inference(resolution, [status(thm)], [c_4, c_8027])).
% 10.08/3.99  tff(c_9755, plain, (![B_619]: (v1_xboole_0(k2_zfmisc_1(B_619, '#skF_8')))), inference(resolution, [status(thm)], [c_9712, c_7910])).
% 10.08/3.99  tff(c_7912, plain, (![C_506]: (~r2_hidden(C_506, '#skF_8'))), inference(splitRight, [status(thm)], [c_460])).
% 10.08/3.99  tff(c_7922, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_52, c_7912])).
% 10.08/3.99  tff(c_7963, plain, (![A_84]: (~v1_xboole_0(A_84) | A_84='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7922, c_95])).
% 10.08/3.99  tff(c_9763, plain, (![B_619]: (k2_zfmisc_1(B_619, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_9755, c_7963])).
% 10.08/3.99  tff(c_8240, plain, (![A_525, B_526, C_527]: (k2_zfmisc_1(k2_zfmisc_1(A_525, B_526), C_527)=k3_zfmisc_1(A_525, B_526, C_527))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.08/3.99  tff(c_10273, plain, (![A_642, A_643, B_644, C_645]: (r2_hidden(k1_mcart_1(A_642), k2_zfmisc_1(A_643, B_644)) | ~r2_hidden(A_642, k3_zfmisc_1(A_643, B_644, C_645)))), inference(superposition, [status(thm), theory('equality')], [c_8240, c_42])).
% 10.08/3.99  tff(c_10291, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_56, c_10273])).
% 10.08/3.99  tff(c_10299, plain, (r2_hidden(k1_mcart_1('#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9763, c_10291])).
% 10.08/3.99  tff(c_10301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7910, c_10299])).
% 10.08/3.99  tff(c_10302, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8') | ~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_54])).
% 10.08/3.99  tff(c_10446, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_10302])).
% 10.08/3.99  tff(c_11658, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_11657, c_10446])).
% 10.08/3.99  tff(c_10837, plain, (![A_696, C_697, B_698]: (r2_hidden(k2_mcart_1(A_696), C_697) | ~r2_hidden(A_696, k2_zfmisc_1(B_698, C_697)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.08/3.99  tff(c_12239, plain, (![A_780, C_781, A_782, B_783]: (r2_hidden(k2_mcart_1(A_780), C_781) | ~r2_hidden(A_780, k3_zfmisc_1(A_782, B_783, C_781)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_10837])).
% 10.08/3.99  tff(c_12247, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_56, c_12239])).
% 10.08/3.99  tff(c_12253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11658, c_12247])).
% 10.08/3.99  tff(c_12254, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_11215])).
% 10.08/3.99  tff(c_12256, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_12254])).
% 10.08/3.99  tff(c_10318, plain, (k3_xboole_0('#skF_8', '#skF_5')='#skF_8'), inference(resolution, [status(thm)], [c_118, c_10304])).
% 10.08/3.99  tff(c_10536, plain, (![C_674]: (~r1_xboole_0('#skF_8', '#skF_5') | ~r2_hidden(C_674, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10318, c_10527])).
% 10.08/3.99  tff(c_10665, plain, (~r1_xboole_0('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_10536])).
% 10.08/3.99  tff(c_10694, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_10506, c_10665])).
% 10.08/3.99  tff(c_12280, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12256, c_10694])).
% 10.08/3.99  tff(c_12299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_12280])).
% 10.08/3.99  tff(c_12301, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_12254])).
% 10.08/3.99  tff(c_11216, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_11111])).
% 10.08/3.99  tff(c_11340, plain, (![A_729, B_730, C_731, D_732]: (k5_mcart_1(A_729, B_730, C_731, D_732)=k1_mcart_1(k1_mcart_1(D_732)) | ~m1_subset_1(D_732, k3_zfmisc_1(A_729, B_730, C_731)) | k1_xboole_0=C_731 | k1_xboole_0=B_730 | k1_xboole_0=A_729)), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.08/3.99  tff(c_11343, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_11340])).
% 10.08/3.99  tff(c_11346, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_11216, c_11343])).
% 10.08/3.99  tff(c_12302, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_12301, c_11346])).
% 10.08/3.99  tff(c_12303, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_12302])).
% 10.08/3.99  tff(c_10319, plain, (k3_xboole_0('#skF_9', '#skF_6')='#skF_9'), inference(resolution, [status(thm)], [c_117, c_10304])).
% 10.08/3.99  tff(c_10530, plain, (![C_674]: (~r1_xboole_0('#skF_9', '#skF_6') | ~r2_hidden(C_674, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_10319, c_10527])).
% 10.08/3.99  tff(c_10664, plain, (~r1_xboole_0('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_10530])).
% 10.08/3.99  tff(c_10678, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_10506, c_10664])).
% 10.08/3.99  tff(c_12329, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12303, c_10678])).
% 10.08/3.99  tff(c_12347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_12329])).
% 10.08/3.99  tff(c_12349, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_12302])).
% 10.08/3.99  tff(c_12300, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_12254])).
% 10.08/3.99  tff(c_12350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12349, c_12300])).
% 10.08/3.99  tff(c_12369, plain, (![C_784]: (~r2_hidden(C_784, '#skF_8'))), inference(splitRight, [status(thm)], [c_10536])).
% 10.08/3.99  tff(c_12379, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_52, c_12369])).
% 10.08/3.99  tff(c_10362, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(resolution, [status(thm)], [c_26, c_10346])).
% 10.08/3.99  tff(c_12419, plain, (![A_22]: (k4_xboole_0(A_22, '#skF_8')=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_12379, c_10362])).
% 10.08/3.99  tff(c_44, plain, (![A_35, B_36, C_37, D_39]: (k7_mcart_1(A_35, B_36, C_37, D_39)=k2_mcart_1(D_39) | ~m1_subset_1(D_39, k3_zfmisc_1(A_35, B_36, C_37)) | k1_xboole_0=C_37 | k1_xboole_0=B_36 | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.08/3.99  tff(c_12909, plain, (![A_822, B_823, C_824, D_825]: (k7_mcart_1(A_822, B_823, C_824, D_825)=k2_mcart_1(D_825) | ~m1_subset_1(D_825, k3_zfmisc_1(A_822, B_823, C_824)) | C_824='#skF_8' | B_823='#skF_8' | A_822='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12379, c_12379, c_12379, c_44])).
% 10.08/3.99  tff(c_12913, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | '#skF_6'='#skF_8' | '#skF_5'='#skF_8' | '#skF_8'='#skF_4'), inference(resolution, [status(thm)], [c_58, c_12909])).
% 10.08/3.99  tff(c_13036, plain, ('#skF_8'='#skF_4'), inference(splitLeft, [status(thm)], [c_12913])).
% 10.08/3.99  tff(c_12410, plain, (~r1_tarski('#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12379, c_10605])).
% 10.08/3.99  tff(c_13051, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13036, c_12410])).
% 10.08/3.99  tff(c_13067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_13051])).
% 10.08/3.99  tff(c_13068, plain, ('#skF_5'='#skF_8' | '#skF_6'='#skF_8' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_12913])).
% 10.08/3.99  tff(c_13405, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_13068])).
% 10.08/3.99  tff(c_13815, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_13405, c_10446])).
% 10.08/3.99  tff(c_12605, plain, (![A_796, C_797, B_798]: (r2_hidden(k2_mcart_1(A_796), C_797) | ~r2_hidden(A_796, k2_zfmisc_1(B_798, C_797)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.08/3.99  tff(c_14029, plain, (![A_891, C_892, A_893, B_894]: (r2_hidden(k2_mcart_1(A_891), C_892) | ~r2_hidden(A_891, k3_zfmisc_1(A_893, B_894, C_892)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_12605])).
% 10.08/3.99  tff(c_14037, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_56, c_14029])).
% 10.08/3.99  tff(c_14043, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13815, c_14037])).
% 10.08/3.99  tff(c_14044, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_13068])).
% 10.08/3.99  tff(c_14176, plain, ('#skF_5'='#skF_8'), inference(splitLeft, [status(thm)], [c_14044])).
% 10.08/3.99  tff(c_10463, plain, (![B_659, A_660]: (B_659=A_660 | ~r1_tarski(B_659, A_660) | ~r1_tarski(A_660, B_659))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.08/3.99  tff(c_10473, plain, ('#skF_5'='#skF_8' | ~r1_tarski('#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_118, c_10463])).
% 10.08/3.99  tff(c_10498, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_10473])).
% 10.08/3.99  tff(c_14177, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14176, c_10498])).
% 10.08/3.99  tff(c_14184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14177])).
% 10.08/3.99  tff(c_14185, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_14044])).
% 10.08/3.99  tff(c_12368, plain, (k4_xboole_0('#skF_9', '#skF_6')!='#skF_9'), inference(resolution, [status(thm)], [c_32, c_10664])).
% 10.08/3.99  tff(c_14198, plain, (k4_xboole_0('#skF_9', '#skF_8')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_14185, c_12368])).
% 10.08/3.99  tff(c_14211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12419, c_14198])).
% 10.08/3.99  tff(c_14212, plain, (![C_674]: (~r2_hidden(C_674, '#skF_9'))), inference(splitRight, [status(thm)], [c_10530])).
% 10.08/3.99  tff(c_14537, plain, (![A_927, B_928, C_929]: (k2_zfmisc_1(k2_zfmisc_1(A_927, B_928), C_929)=k3_zfmisc_1(A_927, B_928, C_929))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.08/3.99  tff(c_15820, plain, (![A_1007, C_1008, A_1009, B_1010]: (r2_hidden(k2_mcart_1(A_1007), C_1008) | ~r2_hidden(A_1007, k3_zfmisc_1(A_1009, B_1010, C_1008)))), inference(superposition, [status(thm), theory('equality')], [c_14537, c_40])).
% 10.08/3.99  tff(c_15828, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_56, c_15820])).
% 10.08/3.99  tff(c_15834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14212, c_15828])).
% 10.08/3.99  tff(c_15835, plain, (![C_674]: (~r2_hidden(C_674, '#skF_7'))), inference(splitRight, [status(thm)], [c_10533])).
% 10.08/3.99  tff(c_10303, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 10.08/3.99  tff(c_15838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15835, c_10303])).
% 10.08/3.99  tff(c_15839, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_10473])).
% 10.08/3.99  tff(c_15845, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_15839, c_58])).
% 10.08/3.99  tff(c_16773, plain, (![A_1075, B_1076, C_1077, D_1078]: (k7_mcart_1(A_1075, B_1076, C_1077, D_1078)=k2_mcart_1(D_1078) | ~m1_subset_1(D_1078, k3_zfmisc_1(A_1075, B_1076, C_1077)) | k1_xboole_0=C_1077 | k1_xboole_0=B_1076 | k1_xboole_0=A_1075)), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.08/3.99  tff(c_16777, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_15845, c_16773])).
% 10.08/3.99  tff(c_16830, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_16777])).
% 10.08/3.99  tff(c_15859, plain, (![A_1011, A_1012]: (r1_xboole_0(A_1011, A_1012) | ~r1_tarski(A_1011, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10360, c_10480])).
% 10.08/3.99  tff(c_15866, plain, (![A_1012, A_1011]: (r1_xboole_0(A_1012, A_1011) | ~r1_tarski(A_1011, k1_xboole_0))), inference(resolution, [status(thm)], [c_15859, c_6])).
% 10.08/3.99  tff(c_15875, plain, (![A_1015, B_1016, C_1017]: (~r1_xboole_0(A_1015, B_1016) | ~r2_hidden(C_1017, k3_xboole_0(A_1015, B_1016)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.08/3.99  tff(c_15881, plain, (![C_1017]: (~r1_xboole_0('#skF_7', '#skF_4') | ~r2_hidden(C_1017, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10317, c_15875])).
% 10.08/3.99  tff(c_15941, plain, (~r1_xboole_0('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_15881])).
% 10.08/3.99  tff(c_15954, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_15866, c_15941])).
% 10.08/3.99  tff(c_16851, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16830, c_15954])).
% 10.08/3.99  tff(c_16864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_16851])).
% 10.08/3.99  tff(c_16865, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_6' | k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_16777])).
% 10.08/3.99  tff(c_17040, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_16865])).
% 10.08/3.99  tff(c_15841, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15839, c_10446])).
% 10.08/3.99  tff(c_17041, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_17040, c_15841])).
% 10.08/3.99  tff(c_16423, plain, (![A_1057, B_1058, C_1059]: (k2_zfmisc_1(k2_zfmisc_1(A_1057, B_1058), C_1059)=k3_zfmisc_1(A_1057, B_1058, C_1059))), inference(cnfTransformation, [status(thm)], [f_85])).
% 10.08/3.99  tff(c_17823, plain, (![A_1134, C_1135, A_1136, B_1137]: (r2_hidden(k2_mcart_1(A_1134), C_1135) | ~r2_hidden(A_1134, k3_zfmisc_1(A_1136, B_1137, C_1135)))), inference(superposition, [status(thm), theory('equality')], [c_16423, c_40])).
% 10.08/3.99  tff(c_17828, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_56, c_17823])).
% 10.08/3.99  tff(c_17833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17041, c_17828])).
% 10.08/3.99  tff(c_17834, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_16865])).
% 10.08/3.99  tff(c_17836, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_17834])).
% 10.08/3.99  tff(c_10320, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_16, c_10304])).
% 10.08/3.99  tff(c_15895, plain, (![B_1018, C_1019]: (~r1_xboole_0(B_1018, B_1018) | ~r2_hidden(C_1019, B_1018))), inference(superposition, [status(thm), theory('equality')], [c_10320, c_15875])).
% 10.08/3.99  tff(c_15918, plain, (![C_1019]: (~r2_hidden(C_1019, k1_xboole_0))), inference(resolution, [status(thm)], [c_76, c_15895])).
% 10.08/3.99  tff(c_17863, plain, (![C_1019]: (~r2_hidden(C_1019, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17836, c_15918])).
% 10.08/3.99  tff(c_10359, plain, (![B_24, A_23]: (k4_xboole_0(B_24, k4_xboole_0(A_23, B_24))=B_24)), inference(resolution, [status(thm)], [c_75, c_10346])).
% 10.08/3.99  tff(c_15958, plain, (![A_1021, B_1022, C_1023]: (r1_tarski(A_1021, B_1022) | ~r1_tarski(A_1021, k4_xboole_0(B_1022, C_1023)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.08/3.99  tff(c_15973, plain, (![B_1024, C_1025]: (r1_tarski(k4_xboole_0(B_1024, C_1025), B_1024))), inference(resolution, [status(thm)], [c_16, c_15958])).
% 10.08/3.99  tff(c_16335, plain, (![B_1051, C_1052, C_1053]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_1051, C_1052), C_1053), C_1052))), inference(resolution, [status(thm)], [c_15973, c_18])).
% 10.08/3.99  tff(c_16505, plain, (![B_1066, C_1067, A_1068]: (r1_xboole_0(k4_xboole_0(B_1066, C_1067), k4_xboole_0(A_1068, B_1066)))), inference(superposition, [status(thm), theory('equality')], [c_10359, c_16335])).
% 10.08/3.99  tff(c_16247, plain, (![A_1044, B_1045]: (~r1_xboole_0(A_1044, B_1045) | v1_xboole_0(k3_xboole_0(A_1044, B_1045)))), inference(resolution, [status(thm)], [c_4, c_15875])).
% 10.08/3.99  tff(c_16271, plain, (![B_13]: (~r1_xboole_0(B_13, B_13) | v1_xboole_0(B_13))), inference(superposition, [status(thm), theory('equality')], [c_10320, c_16247])).
% 10.08/3.99  tff(c_16553, plain, (![A_1069]: (v1_xboole_0(k4_xboole_0(A_1069, A_1069)))), inference(resolution, [status(thm)], [c_16505, c_16271])).
% 10.08/3.99  tff(c_16564, plain, (![A_1069]: (k4_xboole_0(A_1069, A_1069)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16553, c_95])).
% 10.08/3.99  tff(c_10447, plain, (![A_655, B_656]: (r1_xboole_0(A_655, B_656) | k4_xboole_0(A_655, B_656)!=A_655)), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.08/3.99  tff(c_10454, plain, (![B_656, A_655]: (r1_xboole_0(B_656, A_655) | k4_xboole_0(A_655, B_656)!=A_655)), inference(resolution, [status(thm)], [c_10447, c_6])).
% 10.08/3.99  tff(c_16291, plain, (![B_1049]: (~r1_xboole_0(B_1049, B_1049) | v1_xboole_0(B_1049))), inference(superposition, [status(thm), theory('equality')], [c_10320, c_16247])).
% 10.08/3.99  tff(c_16318, plain, (![A_655]: (v1_xboole_0(A_655) | k4_xboole_0(A_655, A_655)!=A_655)), inference(resolution, [status(thm)], [c_10454, c_16291])).
% 10.08/3.99  tff(c_16572, plain, (![A_655]: (v1_xboole_0(A_655) | k1_xboole_0!=A_655)), inference(demodulation, [status(thm), theory('equality')], [c_16564, c_16318])).
% 10.08/3.99  tff(c_17845, plain, (![A_655]: (v1_xboole_0(A_655) | A_655!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17836, c_16572])).
% 10.08/3.99  tff(c_16205, plain, (![A_1039, C_1040, B_1041]: (r2_hidden(k2_mcart_1(A_1039), C_1040) | ~r2_hidden(A_1039, k2_zfmisc_1(B_1041, C_1040)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.08/3.99  tff(c_18824, plain, (![B_1185, C_1186]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1185, C_1186))), C_1186) | v1_xboole_0(k2_zfmisc_1(B_1185, C_1186)))), inference(resolution, [status(thm)], [c_4, c_16205])).
% 10.08/3.99  tff(c_18950, plain, (![C_1194, B_1195]: (~v1_xboole_0(C_1194) | v1_xboole_0(k2_zfmisc_1(B_1195, C_1194)))), inference(resolution, [status(thm)], [c_18824, c_2])).
% 10.08/3.99  tff(c_17868, plain, (![A_84]: (~v1_xboole_0(A_84) | A_84='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17836, c_95])).
% 10.08/3.99  tff(c_18963, plain, (![B_1196, C_1197]: (k2_zfmisc_1(B_1196, C_1197)='#skF_8' | ~v1_xboole_0(C_1197))), inference(resolution, [status(thm)], [c_18950, c_17868])).
% 10.08/3.99  tff(c_19178, plain, (![B_1196]: (k2_zfmisc_1(B_1196, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_17845, c_18963])).
% 10.08/3.99  tff(c_20402, plain, (![A_1254, A_1255, B_1256, C_1257]: (r2_hidden(k1_mcart_1(A_1254), k2_zfmisc_1(A_1255, B_1256)) | ~r2_hidden(A_1254, k3_zfmisc_1(A_1255, B_1256, C_1257)))), inference(superposition, [status(thm), theory('equality')], [c_16423, c_42])).
% 10.08/3.99  tff(c_20428, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_56, c_20402])).
% 10.08/3.99  tff(c_20439, plain, (r2_hidden(k1_mcart_1('#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_19178, c_20428])).
% 10.08/3.99  tff(c_20441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17863, c_20439])).
% 10.08/3.99  tff(c_20442, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_17834])).
% 10.08/3.99  tff(c_15878, plain, (![C_1017]: (~r1_xboole_0('#skF_9', '#skF_6') | ~r2_hidden(C_1017, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_10319, c_15875])).
% 10.08/3.99  tff(c_16003, plain, (~r1_xboole_0('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_15878])).
% 10.08/3.99  tff(c_16016, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_15866, c_16003])).
% 10.08/3.99  tff(c_20467, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20442, c_16016])).
% 10.08/3.99  tff(c_20482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_20467])).
% 10.08/3.99  tff(c_20483, plain, (![C_1017]: (~r2_hidden(C_1017, '#skF_9'))), inference(splitRight, [status(thm)], [c_15878])).
% 10.08/3.99  tff(c_20885, plain, (![A_1286, C_1287, B_1288]: (r2_hidden(k2_mcart_1(A_1286), C_1287) | ~r2_hidden(A_1286, k2_zfmisc_1(B_1288, C_1287)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.08/3.99  tff(c_22702, plain, (![A_1386, C_1387, A_1388, B_1389]: (r2_hidden(k2_mcart_1(A_1386), C_1387) | ~r2_hidden(A_1386, k3_zfmisc_1(A_1388, B_1389, C_1387)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_20885])).
% 10.08/3.99  tff(c_22713, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_56, c_22702])).
% 10.08/3.99  tff(c_22720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20483, c_22713])).
% 10.08/3.99  tff(c_22721, plain, (![C_1017]: (~r2_hidden(C_1017, '#skF_7'))), inference(splitRight, [status(thm)], [c_15881])).
% 10.08/3.99  tff(c_15843, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_15839, c_10303])).
% 10.08/3.99  tff(c_22724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22721, c_15843])).
% 10.08/3.99  tff(c_22725, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_10302])).
% 10.08/3.99  tff(c_23489, plain, (![A_1450, B_1451, C_1452, D_1453]: (k7_mcart_1(A_1450, B_1451, C_1452, D_1453)=k2_mcart_1(D_1453) | ~m1_subset_1(D_1453, k3_zfmisc_1(A_1450, B_1451, C_1452)) | k1_xboole_0=C_1452 | k1_xboole_0=B_1451 | k1_xboole_0=A_1450)), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.08/3.99  tff(c_23493, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_23489])).
% 10.08/3.99  tff(c_23566, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_23493])).
% 10.08/3.99  tff(c_22943, plain, (![A_1413, C_1414, B_1415]: (r1_xboole_0(A_1413, C_1414) | ~r1_xboole_0(B_1415, C_1414) | ~r1_tarski(A_1413, B_1415))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.08/3.99  tff(c_22963, plain, (![A_1416, A_1417]: (r1_xboole_0(A_1416, A_1417) | ~r1_tarski(A_1416, k1_xboole_0))), inference(resolution, [status(thm)], [c_76, c_22943])).
% 10.08/3.99  tff(c_23014, plain, (![A_1421, A_1422]: (r1_xboole_0(A_1421, A_1422) | ~r1_tarski(A_1422, k1_xboole_0))), inference(resolution, [status(thm)], [c_22963, c_6])).
% 10.08/3.99  tff(c_22841, plain, (![A_1404, B_1405, C_1406]: (~r1_xboole_0(A_1404, B_1405) | ~r2_hidden(C_1406, k3_xboole_0(A_1404, B_1405)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.08/3.99  tff(c_22847, plain, (![C_1406]: (~r1_xboole_0('#skF_7', '#skF_4') | ~r2_hidden(C_1406, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_10317, c_22841])).
% 10.08/3.99  tff(c_22986, plain, (~r1_xboole_0('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_22847])).
% 10.08/3.99  tff(c_23034, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_23014, c_22986])).
% 10.08/3.99  tff(c_23579, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23566, c_23034])).
% 10.08/3.99  tff(c_23595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_23579])).
% 10.08/3.99  tff(c_23597, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_23493])).
% 10.08/3.99  tff(c_23786, plain, (![A_1472, B_1473, C_1474, D_1475]: (k5_mcart_1(A_1472, B_1473, C_1474, D_1475)=k1_mcart_1(k1_mcart_1(D_1475)) | ~m1_subset_1(D_1475, k3_zfmisc_1(A_1472, B_1473, C_1474)) | k1_xboole_0=C_1474 | k1_xboole_0=B_1473 | k1_xboole_0=A_1472)), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.08/3.99  tff(c_23789, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_23786])).
% 10.08/3.99  tff(c_23792, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_23597, c_23789])).
% 10.08/3.99  tff(c_24270, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_23792])).
% 10.08/3.99  tff(c_22850, plain, (![C_1406]: (~r1_xboole_0('#skF_8', '#skF_5') | ~r2_hidden(C_1406, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10318, c_22841])).
% 10.08/3.99  tff(c_22926, plain, (~r1_xboole_0('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_22850])).
% 10.08/3.99  tff(c_23036, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_23014, c_22926])).
% 10.08/3.99  tff(c_24300, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24270, c_23036])).
% 10.08/3.99  tff(c_24316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_24300])).
% 10.08/3.99  tff(c_24318, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_23792])).
% 10.08/3.99  tff(c_22747, plain, (![A_1394, B_1395, C_1396]: (r1_tarski(A_1394, B_1395) | ~r1_tarski(A_1394, k4_xboole_0(B_1395, C_1396)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.08/3.99  tff(c_22761, plain, (![B_1395, C_1396]: (r1_tarski(k4_xboole_0(B_1395, C_1396), B_1395))), inference(resolution, [status(thm)], [c_16, c_22747])).
% 10.08/3.99  tff(c_22893, plain, (![A_1410, C_1411, B_1412]: (r1_xboole_0(A_1410, C_1411) | ~r1_tarski(A_1410, k4_xboole_0(B_1412, C_1411)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.08/3.99  tff(c_23502, plain, (![B_1455, C_1456, C_1457]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_1455, C_1456), C_1457), C_1456))), inference(resolution, [status(thm)], [c_22761, c_22893])).
% 10.08/3.99  tff(c_23634, plain, (![B_1467, C_1468, A_1469]: (r1_xboole_0(k4_xboole_0(B_1467, C_1468), k4_xboole_0(A_1469, B_1467)))), inference(superposition, [status(thm), theory('equality')], [c_10359, c_23502])).
% 10.08/3.99  tff(c_23271, plain, (![A_1441, B_1442]: (~r1_xboole_0(A_1441, B_1442) | v1_xboole_0(k3_xboole_0(A_1441, B_1442)))), inference(resolution, [status(thm)], [c_4, c_22841])).
% 10.08/3.99  tff(c_23298, plain, (![B_13]: (~r1_xboole_0(B_13, B_13) | v1_xboole_0(B_13))), inference(superposition, [status(thm), theory('equality')], [c_10320, c_23271])).
% 10.08/3.99  tff(c_23682, plain, (![A_1470]: (v1_xboole_0(k4_xboole_0(A_1470, A_1470)))), inference(resolution, [status(thm)], [c_23634, c_23298])).
% 10.08/3.99  tff(c_23696, plain, (![A_1470]: (k4_xboole_0(A_1470, A_1470)=k1_xboole_0)), inference(resolution, [status(thm)], [c_23682, c_95])).
% 10.08/3.99  tff(c_24357, plain, (![A_1506, B_1507, A_1508]: (r1_xboole_0(A_1506, B_1507) | ~r1_tarski(A_1506, A_1508) | k4_xboole_0(A_1508, B_1507)!=A_1508)), inference(resolution, [status(thm)], [c_32, c_22943])).
% 10.08/3.99  tff(c_24440, plain, (![B_1511]: (r1_xboole_0('#skF_9', B_1511) | k4_xboole_0('#skF_6', B_1511)!='#skF_6')), inference(resolution, [status(thm)], [c_117, c_24357])).
% 10.08/3.99  tff(c_22844, plain, (![C_1406]: (~r1_xboole_0('#skF_9', '#skF_6') | ~r2_hidden(C_1406, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_10319, c_22841])).
% 10.08/3.99  tff(c_22925, plain, (~r1_xboole_0('#skF_9', '#skF_6')), inference(splitLeft, [status(thm)], [c_22844])).
% 10.08/3.99  tff(c_24452, plain, (k4_xboole_0('#skF_6', '#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_24440, c_22925])).
% 10.08/3.99  tff(c_24466, plain, (k1_xboole_0!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_23696, c_24452])).
% 10.08/3.99  tff(c_23598, plain, (![A_1460, B_1461, C_1462, D_1463]: (k6_mcart_1(A_1460, B_1461, C_1462, D_1463)=k2_mcart_1(k1_mcart_1(D_1463)) | ~m1_subset_1(D_1463, k3_zfmisc_1(A_1460, B_1461, C_1462)) | k1_xboole_0=C_1462 | k1_xboole_0=B_1461 | k1_xboole_0=A_1460)), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.08/3.99  tff(c_23601, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_23598])).
% 10.08/3.99  tff(c_23604, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_23597, c_23601])).
% 10.08/3.99  tff(c_24648, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_24318, c_24466, c_23604])).
% 10.08/3.99  tff(c_23100, plain, (![A_1427, B_1428, C_1429]: (r2_hidden(k1_mcart_1(A_1427), B_1428) | ~r2_hidden(A_1427, k2_zfmisc_1(B_1428, C_1429)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.08/3.99  tff(c_27039, plain, (![A_1605, A_1606, B_1607, C_1608]: (r2_hidden(k1_mcart_1(A_1605), k2_zfmisc_1(A_1606, B_1607)) | ~r2_hidden(A_1605, k3_zfmisc_1(A_1606, B_1607, C_1608)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_23100])).
% 10.08/3.99  tff(c_27079, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_56, c_27039])).
% 10.08/3.99  tff(c_27084, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_27079, c_40])).
% 10.08/3.99  tff(c_27101, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24648, c_27084])).
% 10.08/3.99  tff(c_27103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22725, c_27101])).
% 10.08/3.99  tff(c_27104, plain, (![C_1406]: (~r2_hidden(C_1406, '#skF_7'))), inference(splitRight, [status(thm)], [c_22847])).
% 10.08/3.99  tff(c_27107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27104, c_10303])).
% 10.08/3.99  tff(c_27108, plain, (![C_1406]: (~r2_hidden(C_1406, '#skF_8'))), inference(splitRight, [status(thm)], [c_22850])).
% 10.08/3.99  tff(c_27289, plain, (![A_1617, C_1618, B_1619]: (r2_hidden(k2_mcart_1(A_1617), C_1618) | ~r2_hidden(A_1617, k2_zfmisc_1(B_1619, C_1618)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.08/3.99  tff(c_28839, plain, (![B_1720, C_1721]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1720, C_1721))), C_1721) | v1_xboole_0(k2_zfmisc_1(B_1720, C_1721)))), inference(resolution, [status(thm)], [c_4, c_27289])).
% 10.08/3.99  tff(c_28882, plain, (![B_1722]: (v1_xboole_0(k2_zfmisc_1(B_1722, '#skF_8')))), inference(resolution, [status(thm)], [c_28839, c_27108])).
% 10.08/3.99  tff(c_27119, plain, (![C_1609]: (~r2_hidden(C_1609, '#skF_8'))), inference(splitRight, [status(thm)], [c_22850])).
% 10.08/3.99  tff(c_27129, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_52, c_27119])).
% 10.08/3.99  tff(c_27138, plain, (![A_84]: (~v1_xboole_0(A_84) | A_84='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_27129, c_95])).
% 10.08/3.99  tff(c_28890, plain, (![B_1722]: (k2_zfmisc_1(B_1722, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_28882, c_27138])).
% 10.08/3.99  tff(c_27442, plain, (![A_1629, B_1630, C_1631]: (r2_hidden(k1_mcart_1(A_1629), B_1630) | ~r2_hidden(A_1629, k2_zfmisc_1(B_1630, C_1631)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.08/3.99  tff(c_29369, plain, (![A_1743, A_1744, B_1745, C_1746]: (r2_hidden(k1_mcart_1(A_1743), k2_zfmisc_1(A_1744, B_1745)) | ~r2_hidden(A_1743, k3_zfmisc_1(A_1744, B_1745, C_1746)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_27442])).
% 10.08/3.99  tff(c_29387, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_56, c_29369])).
% 10.08/3.99  tff(c_29395, plain, (r2_hidden(k1_mcart_1('#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28890, c_29387])).
% 10.08/3.99  tff(c_29397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27108, c_29395])).
% 10.08/3.99  tff(c_29398, plain, (![C_1406]: (~r2_hidden(C_1406, '#skF_9'))), inference(splitRight, [status(thm)], [c_22844])).
% 10.08/3.99  tff(c_22726, plain, (r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_10302])).
% 10.08/3.99  tff(c_29401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29398, c_22726])).
% 10.08/3.99  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.08/3.99  
% 10.08/3.99  Inference rules
% 10.08/3.99  ----------------------
% 10.08/3.99  #Ref     : 0
% 10.08/3.99  #Sup     : 6644
% 10.08/3.99  #Fact    : 0
% 10.08/3.99  #Define  : 0
% 10.08/3.99  #Split   : 67
% 10.08/3.99  #Chain   : 0
% 10.08/3.99  #Close   : 0
% 10.08/3.99  
% 10.08/3.99  Ordering : KBO
% 10.08/3.99  
% 10.08/3.99  Simplification rules
% 10.08/3.99  ----------------------
% 10.08/3.99  #Subsume      : 1093
% 10.08/3.99  #Demod        : 5144
% 10.08/3.99  #Tautology    : 3636
% 10.08/3.99  #SimpNegUnit  : 335
% 10.08/3.99  #BackRed      : 1080
% 10.08/3.99  
% 10.08/3.99  #Partial instantiations: 0
% 10.08/3.99  #Strategies tried      : 1
% 10.08/3.99  
% 10.08/3.99  Timing (in seconds)
% 10.08/3.99  ----------------------
% 10.08/3.99  Preprocessing        : 0.35
% 10.08/3.99  Parsing              : 0.18
% 10.08/3.99  CNF conversion       : 0.03
% 10.08/3.99  Main loop            : 2.79
% 10.08/3.99  Inferencing          : 0.82
% 10.08/3.99  Reduction            : 1.07
% 10.08/3.99  Demodulation         : 0.73
% 10.08/3.99  BG Simplification    : 0.08
% 10.08/3.99  Subsumption          : 0.57
% 10.08/3.99  Abstraction          : 0.10
% 10.08/3.99  MUC search           : 0.00
% 10.08/3.99  Cooper               : 0.00
% 10.08/3.99  Total                : 3.25
% 10.08/3.99  Index Insertion      : 0.00
% 10.08/3.99  Index Deletion       : 0.00
% 10.08/3.99  Index Matching       : 0.00
% 10.08/3.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
