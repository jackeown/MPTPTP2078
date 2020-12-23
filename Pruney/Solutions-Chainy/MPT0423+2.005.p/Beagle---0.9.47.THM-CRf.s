%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:52 EST 2020

% Result     : Theorem 6.03s
% Output     : CNFRefutation 6.03s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 148 expanded)
%              Number of leaves         :   50 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  154 ( 230 expanded)
%              Number of equality atoms :   51 (  84 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_74,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_108,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_162,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B = k1_tarski(A)
         => k7_setfam_1(A,B) = k1_tarski(k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_76,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_113,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_146,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_127,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_129,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_125,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_155,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

tff(c_104,plain,(
    ! [A_55] : ~ v1_xboole_0(k1_zfmisc_1(A_55)) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_44,plain,(
    ! [A_40] : k1_subset_1(A_40) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_102,plain,(
    ! [A_54] : m1_subset_1(k1_subset_1(A_54),k1_zfmisc_1(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_132,plain,(
    ! [A_54] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_54)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_102])).

tff(c_38,plain,(
    ! [B_39,A_38] :
      ( r2_hidden(B_39,A_38)
      | ~ m1_subset_1(B_39,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_126,plain,(
    k7_setfam_1('#skF_3','#skF_4') != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_32,plain,(
    ! [B_37] : r1_tarski(k1_tarski(B_37),k1_tarski(B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_241,plain,(
    ! [A_93,B_94] :
      ( r2_hidden(A_93,B_94)
      | ~ r1_tarski(k1_tarski(A_93),B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_252,plain,(
    ! [B_37] : r2_hidden(B_37,k1_tarski(B_37)) ),
    inference(resolution,[status(thm)],[c_32,c_241])).

tff(c_108,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k1_tarski(A_57),k1_zfmisc_1(B_58))
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    ! [A_41] : k2_subset_1(A_41) = A_41 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_106,plain,(
    ! [A_56] : k3_subset_1(A_56,k1_subset_1(A_56)) = k2_subset_1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_131,plain,(
    ! [A_56] : k3_subset_1(A_56,k1_subset_1(A_56)) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_106])).

tff(c_133,plain,(
    ! [A_56] : k3_subset_1(A_56,k1_xboole_0) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_131])).

tff(c_1565,plain,(
    ! [A_356,C_357,B_358] :
      ( r2_hidden(k3_subset_1(A_356,C_357),k7_setfam_1(A_356,B_358))
      | ~ r2_hidden(C_357,B_358)
      | ~ m1_subset_1(C_357,k1_zfmisc_1(A_356))
      | ~ m1_subset_1(B_358,k1_zfmisc_1(k1_zfmisc_1(A_356))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1583,plain,(
    ! [A_56,B_358] :
      ( r2_hidden(A_56,k7_setfam_1(A_56,B_358))
      | ~ r2_hidden(k1_xboole_0,B_358)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_358,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_1565])).

tff(c_2431,plain,(
    ! [A_653,B_654] :
      ( r2_hidden(A_653,k7_setfam_1(A_653,B_654))
      | ~ r2_hidden(k1_xboole_0,B_654)
      | ~ m1_subset_1(B_654,k1_zfmisc_1(k1_zfmisc_1(A_653))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1583])).

tff(c_2849,plain,(
    ! [A_720,A_721] :
      ( r2_hidden(A_720,k7_setfam_1(A_720,k1_tarski(A_721)))
      | ~ r2_hidden(k1_xboole_0,k1_tarski(A_721))
      | ~ r2_hidden(A_721,k1_zfmisc_1(A_720)) ) ),
    inference(resolution,[status(thm)],[c_108,c_2431])).

tff(c_128,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_219,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k1_tarski(A_88),B_89)
      | ~ r2_hidden(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_222,plain,(
    ! [B_89] :
      ( r1_tarski('#skF_4',B_89)
      | ~ r2_hidden('#skF_3',B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_219])).

tff(c_2864,plain,(
    ! [A_721] :
      ( r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_721)))
      | ~ r2_hidden(k1_xboole_0,k1_tarski(A_721))
      | ~ r2_hidden(A_721,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2849,c_222])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_114,plain,(
    ! [A_63] : k1_setfam_1(k1_tarski(A_63)) = A_63 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_282,plain,(
    ! [A_99,B_100] : k1_setfam_1(k2_tarski(A_99,B_100)) = k3_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_291,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_282])).

tff(c_294,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_291])).

tff(c_347,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k3_xboole_0(A_109,B_110)) = k4_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_356,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k4_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_347])).

tff(c_359,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_356])).

tff(c_304,plain,(
    ! [B_102] : k4_xboole_0(k1_tarski(B_102),k1_tarski(B_102)) != k1_tarski(B_102) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_307,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_3')) != k1_tarski('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_304])).

tff(c_311,plain,(
    k4_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_128,c_307])).

tff(c_360,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_311])).

tff(c_130,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_692,plain,(
    ! [A_188,B_189] :
      ( k7_setfam_1(A_188,B_189) != k1_xboole_0
      | k1_xboole_0 = B_189
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k1_zfmisc_1(A_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_707,plain,
    ( k7_setfam_1('#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_130,c_692])).

tff(c_724,plain,(
    k7_setfam_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_707])).

tff(c_110,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k7_setfam_1(A_59,B_60),k1_zfmisc_1(k1_zfmisc_1(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_727,plain,(
    ! [A_190,B_191] :
      ( k7_setfam_1(A_190,k7_setfam_1(A_190,B_191)) = B_191
      | ~ m1_subset_1(B_191,k1_zfmisc_1(k1_zfmisc_1(A_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_747,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_130,c_727])).

tff(c_1659,plain,(
    ! [C_389,B_390,A_391] :
      ( r2_hidden(C_389,B_390)
      | ~ r2_hidden(k3_subset_1(A_391,C_389),k7_setfam_1(A_391,B_390))
      | ~ m1_subset_1(C_389,k1_zfmisc_1(A_391))
      | ~ m1_subset_1(B_390,k1_zfmisc_1(k1_zfmisc_1(A_391))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1674,plain,(
    ! [C_389] :
      ( r2_hidden(C_389,k7_setfam_1('#skF_3','#skF_4'))
      | ~ r2_hidden(k3_subset_1('#skF_3',C_389),'#skF_4')
      | ~ m1_subset_1(C_389,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_1659])).

tff(c_2267,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1674])).

tff(c_2270,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_110,c_2267])).

tff(c_2277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_2270])).

tff(c_2279,plain,(
    m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1674])).

tff(c_1782,plain,(
    ! [B_424,C_425,A_426] :
      ( r1_tarski(B_424,C_425)
      | ~ r1_tarski(k7_setfam_1(A_426,B_424),k7_setfam_1(A_426,C_425))
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k1_zfmisc_1(A_426)))
      | ~ m1_subset_1(B_424,k1_zfmisc_1(k1_zfmisc_1(A_426))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1803,plain,(
    ! [C_425] :
      ( r1_tarski(k7_setfam_1('#skF_3','#skF_4'),C_425)
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',C_425))
      | ~ m1_subset_1(C_425,k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_747,c_1782])).

tff(c_2758,plain,(
    ! [C_709] :
      ( r1_tarski(k7_setfam_1('#skF_3','#skF_4'),C_709)
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',C_709))
      | ~ m1_subset_1(C_709,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2279,c_1803])).

tff(c_3227,plain,(
    ! [A_787] :
      ( r1_tarski(k7_setfam_1('#skF_3','#skF_4'),k1_tarski(A_787))
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_787)))
      | ~ r2_hidden(A_787,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_108,c_2758])).

tff(c_30,plain,(
    ! [B_37,A_36] :
      ( k1_tarski(B_37) = A_36
      | k1_xboole_0 = A_36
      | ~ r1_tarski(A_36,k1_tarski(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3230,plain,(
    ! [A_787] :
      ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(A_787)
      | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_787)))
      | ~ r2_hidden(A_787,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3227,c_30])).

tff(c_3239,plain,(
    ! [A_788] :
      ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(A_788)
      | ~ r1_tarski('#skF_4',k7_setfam_1('#skF_3',k1_tarski(A_788)))
      | ~ r2_hidden(A_788,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_724,c_3230])).

tff(c_3252,plain,(
    ! [A_789] :
      ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(A_789)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(A_789))
      | ~ r2_hidden(A_789,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2864,c_3239])).

tff(c_3258,plain,
    ( k7_setfam_1('#skF_3','#skF_4') = k1_tarski(k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_252,c_3252])).

tff(c_3264,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_3258])).

tff(c_3269,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_3'))
    | v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_3264])).

tff(c_3272,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_3269])).

tff(c_3274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_3272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:55:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.03/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.03/2.13  
% 6.03/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.03/2.13  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.03/2.13  
% 6.03/2.13  %Foreground sorts:
% 6.03/2.13  
% 6.03/2.13  
% 6.03/2.13  %Background operators:
% 6.03/2.13  
% 6.03/2.13  
% 6.03/2.13  %Foreground operators:
% 6.03/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.03/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.03/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.03/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.03/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.03/2.13  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 6.03/2.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.03/2.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.03/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.03/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.03/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.03/2.13  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.03/2.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.03/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.03/2.13  tff('#skF_3', type, '#skF_3': $i).
% 6.03/2.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.03/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.03/2.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.03/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.03/2.13  tff('#skF_4', type, '#skF_4': $i).
% 6.03/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.03/2.13  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 6.03/2.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.03/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.03/2.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.03/2.13  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.03/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.03/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.03/2.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.03/2.13  
% 6.03/2.15  tff(f_111, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.03/2.15  tff(f_74, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 6.03/2.15  tff(f_108, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 6.03/2.15  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.03/2.15  tff(f_162, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((B = k1_tarski(A)) => (k7_setfam_1(A, B) = k1_tarski(k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_setfam_1)).
% 6.03/2.15  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 6.03/2.15  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.03/2.15  tff(f_117, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 6.03/2.15  tff(f_76, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.03/2.15  tff(f_113, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 6.03/2.15  tff(f_146, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 6.03/2.15  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.03/2.15  tff(f_127, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 6.03/2.15  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.03/2.15  tff(f_129, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.03/2.15  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.03/2.15  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.03/2.15  tff(f_137, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 6.03/2.15  tff(f_121, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 6.03/2.15  tff(f_125, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 6.03/2.15  tff(f_155, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), k7_setfam_1(A, C)) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_setfam_1)).
% 6.03/2.15  tff(c_104, plain, (![A_55]: (~v1_xboole_0(k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.03/2.15  tff(c_44, plain, (![A_40]: (k1_subset_1(A_40)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.03/2.15  tff(c_102, plain, (![A_54]: (m1_subset_1(k1_subset_1(A_54), k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.03/2.15  tff(c_132, plain, (![A_54]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_54)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_102])).
% 6.03/2.15  tff(c_38, plain, (![B_39, A_38]: (r2_hidden(B_39, A_38) | ~m1_subset_1(B_39, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.03/2.15  tff(c_126, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.03/2.15  tff(c_32, plain, (![B_37]: (r1_tarski(k1_tarski(B_37), k1_tarski(B_37)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.03/2.15  tff(c_241, plain, (![A_93, B_94]: (r2_hidden(A_93, B_94) | ~r1_tarski(k1_tarski(A_93), B_94))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.03/2.15  tff(c_252, plain, (![B_37]: (r2_hidden(B_37, k1_tarski(B_37)))), inference(resolution, [status(thm)], [c_32, c_241])).
% 6.03/2.15  tff(c_108, plain, (![A_57, B_58]: (m1_subset_1(k1_tarski(A_57), k1_zfmisc_1(B_58)) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.03/2.15  tff(c_46, plain, (![A_41]: (k2_subset_1(A_41)=A_41)), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.03/2.15  tff(c_106, plain, (![A_56]: (k3_subset_1(A_56, k1_subset_1(A_56))=k2_subset_1(A_56))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.03/2.15  tff(c_131, plain, (![A_56]: (k3_subset_1(A_56, k1_subset_1(A_56))=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_106])).
% 6.03/2.15  tff(c_133, plain, (![A_56]: (k3_subset_1(A_56, k1_xboole_0)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_131])).
% 6.03/2.15  tff(c_1565, plain, (![A_356, C_357, B_358]: (r2_hidden(k3_subset_1(A_356, C_357), k7_setfam_1(A_356, B_358)) | ~r2_hidden(C_357, B_358) | ~m1_subset_1(C_357, k1_zfmisc_1(A_356)) | ~m1_subset_1(B_358, k1_zfmisc_1(k1_zfmisc_1(A_356))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.03/2.15  tff(c_1583, plain, (![A_56, B_358]: (r2_hidden(A_56, k7_setfam_1(A_56, B_358)) | ~r2_hidden(k1_xboole_0, B_358) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_56)) | ~m1_subset_1(B_358, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(superposition, [status(thm), theory('equality')], [c_133, c_1565])).
% 6.03/2.15  tff(c_2431, plain, (![A_653, B_654]: (r2_hidden(A_653, k7_setfam_1(A_653, B_654)) | ~r2_hidden(k1_xboole_0, B_654) | ~m1_subset_1(B_654, k1_zfmisc_1(k1_zfmisc_1(A_653))))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1583])).
% 6.03/2.15  tff(c_2849, plain, (![A_720, A_721]: (r2_hidden(A_720, k7_setfam_1(A_720, k1_tarski(A_721))) | ~r2_hidden(k1_xboole_0, k1_tarski(A_721)) | ~r2_hidden(A_721, k1_zfmisc_1(A_720)))), inference(resolution, [status(thm)], [c_108, c_2431])).
% 6.03/2.15  tff(c_128, plain, (k1_tarski('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.03/2.15  tff(c_219, plain, (![A_88, B_89]: (r1_tarski(k1_tarski(A_88), B_89) | ~r2_hidden(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.03/2.15  tff(c_222, plain, (![B_89]: (r1_tarski('#skF_4', B_89) | ~r2_hidden('#skF_3', B_89))), inference(superposition, [status(thm), theory('equality')], [c_128, c_219])).
% 6.03/2.15  tff(c_2864, plain, (![A_721]: (r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_721))) | ~r2_hidden(k1_xboole_0, k1_tarski(A_721)) | ~r2_hidden(A_721, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_2849, c_222])).
% 6.03/2.15  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.03/2.15  tff(c_114, plain, (![A_63]: (k1_setfam_1(k1_tarski(A_63))=A_63)), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.03/2.15  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.03/2.15  tff(c_282, plain, (![A_99, B_100]: (k1_setfam_1(k2_tarski(A_99, B_100))=k3_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.03/2.15  tff(c_291, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_282])).
% 6.03/2.15  tff(c_294, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_291])).
% 6.03/2.15  tff(c_347, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k3_xboole_0(A_109, B_110))=k4_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.03/2.15  tff(c_356, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k4_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_294, c_347])).
% 6.03/2.15  tff(c_359, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_356])).
% 6.03/2.15  tff(c_304, plain, (![B_102]: (k4_xboole_0(k1_tarski(B_102), k1_tarski(B_102))!=k1_tarski(B_102))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.03/2.15  tff(c_307, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_3'))!=k1_tarski('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_128, c_304])).
% 6.03/2.15  tff(c_311, plain, (k4_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_128, c_307])).
% 6.03/2.15  tff(c_360, plain, (k1_xboole_0!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_359, c_311])).
% 6.03/2.15  tff(c_130, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 6.03/2.15  tff(c_692, plain, (![A_188, B_189]: (k7_setfam_1(A_188, B_189)!=k1_xboole_0 | k1_xboole_0=B_189 | ~m1_subset_1(B_189, k1_zfmisc_1(k1_zfmisc_1(A_188))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 6.03/2.15  tff(c_707, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_130, c_692])).
% 6.03/2.15  tff(c_724, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_360, c_707])).
% 6.03/2.15  tff(c_110, plain, (![A_59, B_60]: (m1_subset_1(k7_setfam_1(A_59, B_60), k1_zfmisc_1(k1_zfmisc_1(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.03/2.15  tff(c_727, plain, (![A_190, B_191]: (k7_setfam_1(A_190, k7_setfam_1(A_190, B_191))=B_191 | ~m1_subset_1(B_191, k1_zfmisc_1(k1_zfmisc_1(A_190))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.03/2.15  tff(c_747, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_130, c_727])).
% 6.03/2.15  tff(c_1659, plain, (![C_389, B_390, A_391]: (r2_hidden(C_389, B_390) | ~r2_hidden(k3_subset_1(A_391, C_389), k7_setfam_1(A_391, B_390)) | ~m1_subset_1(C_389, k1_zfmisc_1(A_391)) | ~m1_subset_1(B_390, k1_zfmisc_1(k1_zfmisc_1(A_391))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 6.03/2.15  tff(c_1674, plain, (![C_389]: (r2_hidden(C_389, k7_setfam_1('#skF_3', '#skF_4')) | ~r2_hidden(k3_subset_1('#skF_3', C_389), '#skF_4') | ~m1_subset_1(C_389, k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_747, c_1659])).
% 6.03/2.15  tff(c_2267, plain, (~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1674])).
% 6.03/2.15  tff(c_2270, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_110, c_2267])).
% 6.03/2.15  tff(c_2277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_2270])).
% 6.03/2.15  tff(c_2279, plain, (m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1674])).
% 6.03/2.15  tff(c_1782, plain, (![B_424, C_425, A_426]: (r1_tarski(B_424, C_425) | ~r1_tarski(k7_setfam_1(A_426, B_424), k7_setfam_1(A_426, C_425)) | ~m1_subset_1(C_425, k1_zfmisc_1(k1_zfmisc_1(A_426))) | ~m1_subset_1(B_424, k1_zfmisc_1(k1_zfmisc_1(A_426))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.03/2.15  tff(c_1803, plain, (![C_425]: (r1_tarski(k7_setfam_1('#skF_3', '#skF_4'), C_425) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', C_425)) | ~m1_subset_1(C_425, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_747, c_1782])).
% 6.03/2.15  tff(c_2758, plain, (![C_709]: (r1_tarski(k7_setfam_1('#skF_3', '#skF_4'), C_709) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', C_709)) | ~m1_subset_1(C_709, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2279, c_1803])).
% 6.03/2.15  tff(c_3227, plain, (![A_787]: (r1_tarski(k7_setfam_1('#skF_3', '#skF_4'), k1_tarski(A_787)) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_787))) | ~r2_hidden(A_787, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_108, c_2758])).
% 6.03/2.15  tff(c_30, plain, (![B_37, A_36]: (k1_tarski(B_37)=A_36 | k1_xboole_0=A_36 | ~r1_tarski(A_36, k1_tarski(B_37)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.03/2.15  tff(c_3230, plain, (![A_787]: (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(A_787) | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_787))) | ~r2_hidden(A_787, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_3227, c_30])).
% 6.03/2.15  tff(c_3239, plain, (![A_788]: (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(A_788) | ~r1_tarski('#skF_4', k7_setfam_1('#skF_3', k1_tarski(A_788))) | ~r2_hidden(A_788, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_724, c_3230])).
% 6.03/2.15  tff(c_3252, plain, (![A_789]: (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(A_789) | ~r2_hidden(k1_xboole_0, k1_tarski(A_789)) | ~r2_hidden(A_789, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_2864, c_3239])).
% 6.03/2.15  tff(c_3258, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_tarski(k1_xboole_0) | ~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_252, c_3252])).
% 6.03/2.15  tff(c_3264, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_126, c_3258])).
% 6.03/2.15  tff(c_3269, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_3')) | v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_3264])).
% 6.03/2.15  tff(c_3272, plain, (v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_3269])).
% 6.03/2.15  tff(c_3274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_3272])).
% 6.03/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.03/2.15  
% 6.03/2.15  Inference rules
% 6.03/2.15  ----------------------
% 6.03/2.15  #Ref     : 0
% 6.03/2.15  #Sup     : 678
% 6.03/2.15  #Fact    : 0
% 6.03/2.15  #Define  : 0
% 6.03/2.15  #Split   : 9
% 6.03/2.15  #Chain   : 0
% 6.03/2.15  #Close   : 0
% 6.03/2.15  
% 6.03/2.15  Ordering : KBO
% 6.03/2.15  
% 6.03/2.15  Simplification rules
% 6.03/2.15  ----------------------
% 6.03/2.15  #Subsume      : 170
% 6.03/2.15  #Demod        : 238
% 6.03/2.15  #Tautology    : 215
% 6.03/2.15  #SimpNegUnit  : 57
% 6.03/2.15  #BackRed      : 2
% 6.03/2.15  
% 6.03/2.15  #Partial instantiations: 0
% 6.03/2.15  #Strategies tried      : 1
% 6.03/2.15  
% 6.03/2.15  Timing (in seconds)
% 6.03/2.15  ----------------------
% 6.03/2.15  Preprocessing        : 0.38
% 6.03/2.15  Parsing              : 0.19
% 6.03/2.15  CNF conversion       : 0.03
% 6.03/2.15  Main loop            : 0.99
% 6.03/2.15  Inferencing          : 0.35
% 6.03/2.15  Reduction            : 0.32
% 6.03/2.15  Demodulation         : 0.23
% 6.03/2.15  BG Simplification    : 0.04
% 6.03/2.15  Subsumption          : 0.23
% 6.03/2.15  Abstraction          : 0.04
% 6.03/2.15  MUC search           : 0.00
% 6.03/2.15  Cooper               : 0.00
% 6.03/2.15  Total                : 1.41
% 6.03/2.15  Index Insertion      : 0.00
% 6.03/2.15  Index Deletion       : 0.00
% 6.03/2.15  Index Matching       : 0.00
% 6.03/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
