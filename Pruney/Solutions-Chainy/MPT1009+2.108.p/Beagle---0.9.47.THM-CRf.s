%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:57 EST 2020

% Result     : Theorem 12.06s
% Output     : CNFRefutation 12.41s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 979 expanded)
%              Number of leaves         :   61 ( 342 expanded)
%              Depth                    :   15
%              Number of atoms          :  362 (2032 expanded)
%              Number of equality atoms :  133 ( 543 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_113,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_165,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_117,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_143,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_153,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_89,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_147,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_123,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_102,plain,(
    ! [A_58,B_59] : v1_relat_1(k2_zfmisc_1(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_126,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_199,plain,(
    ! [B_94,A_95] :
      ( v1_relat_1(B_94)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_95))
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_205,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_126,c_199])).

tff(c_209,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_205])).

tff(c_104,plain,(
    ! [B_61,A_60] :
      ( r1_tarski(k9_relat_1(B_61,A_60),k2_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_130,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_464,plain,(
    ! [A_139,B_140] :
      ( k9_relat_1(A_139,k1_tarski(B_140)) = k11_relat_1(A_139,B_140)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_424,plain,(
    ! [C_136,A_137,B_138] :
      ( v4_relat_1(C_136,A_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_439,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_126,c_424])).

tff(c_110,plain,(
    ! [B_66,A_65] :
      ( k7_relat_1(B_66,A_65) = B_66
      | ~ v4_relat_1(B_66,A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_442,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_439,c_110])).

tff(c_445,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_442])).

tff(c_106,plain,(
    ! [B_63,A_62] :
      ( k2_relat_1(k7_relat_1(B_63,A_62)) = k9_relat_1(B_63,A_62)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_449,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_106])).

tff(c_453,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_449])).

tff(c_470,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_453])).

tff(c_490,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_470])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [B_35] : k2_zfmisc_1(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_289,plain,(
    ! [B_107,A_108] :
      ( r1_tarski(k1_relat_1(B_107),A_108)
      | ~ v4_relat_1(B_107,A_108)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_24,plain,(
    ! [B_33,A_32] :
      ( k1_tarski(B_33) = A_32
      | k1_xboole_0 = A_32
      | ~ r1_tarski(A_32,k1_tarski(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14684,plain,(
    ! [B_2534,B_2535] :
      ( k1_tarski(B_2534) = k1_relat_1(B_2535)
      | k1_relat_1(B_2535) = k1_xboole_0
      | ~ v4_relat_1(B_2535,k1_tarski(B_2534))
      | ~ v1_relat_1(B_2535) ) ),
    inference(resolution,[status(thm)],[c_289,c_24])).

tff(c_14714,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_439,c_14684])).

tff(c_14727,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_14714])).

tff(c_14728,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14727])).

tff(c_13799,plain,(
    ! [D_2233,B_2234,C_2235,A_2236] :
      ( m1_subset_1(D_2233,k1_zfmisc_1(k2_zfmisc_1(B_2234,C_2235)))
      | ~ r1_tarski(k1_relat_1(D_2233),B_2234)
      | ~ m1_subset_1(D_2233,k1_zfmisc_1(k2_zfmisc_1(A_2236,C_2235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_13827,plain,(
    ! [B_2238] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_2238,'#skF_4')))
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_2238) ) ),
    inference(resolution,[status(thm)],[c_126,c_13799])).

tff(c_90,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_13972,plain,(
    ! [B_2247] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(B_2247,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_2247) ) ),
    inference(resolution,[status(thm)],[c_13827,c_90])).

tff(c_13984,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_13972])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14011,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_13984,c_2])).

tff(c_14162,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_14011])).

tff(c_14730,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,'#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14728,c_14162])).

tff(c_14744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34,c_14730])).

tff(c_14745,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_14727])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_7,B_8,C_9] : k2_enumset1(A_7,A_7,B_8,C_9) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12,D_13] : k3_enumset1(A_10,A_10,B_11,C_12,D_13) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] : k4_enumset1(A_14,A_14,B_15,C_16,D_17,E_18) = k3_enumset1(A_14,B_15,C_16,D_17,E_18) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_19,C_21,D_22,B_20,F_24,E_23] : k5_enumset1(A_19,A_19,B_20,C_21,D_22,E_23,F_24) = k4_enumset1(A_19,B_20,C_21,D_22,E_23,F_24) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13935,plain,(
    ! [G_2241,C_2243,D_2240,A_2242,B_2245,F_2244,E_2246] : k6_enumset1(A_2242,A_2242,B_2245,C_2243,D_2240,E_2246,F_2244,G_2241) = k5_enumset1(A_2242,B_2245,C_2243,D_2240,E_2246,F_2244,G_2241) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [F_41,G_42,D_39,A_36,J_47,H_43,C_38,B_37] : r2_hidden(J_47,k6_enumset1(A_36,B_37,C_38,D_39,J_47,F_41,G_42,H_43)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_14048,plain,(
    ! [E_2252,A_2255,D_2256,B_2258,G_2254,C_2257,F_2253] : r2_hidden(D_2256,k5_enumset1(A_2255,B_2258,C_2257,D_2256,E_2252,F_2253,G_2254)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13935,c_44])).

tff(c_14052,plain,(
    ! [A_2262,B_2261,E_2260,C_2259,F_2263,D_2264] : r2_hidden(C_2259,k4_enumset1(A_2262,B_2261,C_2259,D_2264,E_2260,F_2263)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_14048])).

tff(c_14100,plain,(
    ! [C_2276,E_2274,A_2278,B_2277,D_2275] : r2_hidden(B_2277,k3_enumset1(A_2278,B_2277,C_2276,D_2275,E_2274)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_14052])).

tff(c_14104,plain,(
    ! [A_2279,B_2280,C_2281,D_2282] : r2_hidden(A_2279,k2_enumset1(A_2279,B_2280,C_2281,D_2282)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_14100])).

tff(c_14108,plain,(
    ! [A_2283,B_2284,C_2285] : r2_hidden(A_2283,k1_enumset1(A_2283,B_2284,C_2285)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_14104])).

tff(c_14131,plain,(
    ! [A_2288,B_2289] : r2_hidden(A_2288,k2_tarski(A_2288,B_2289)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_14108])).

tff(c_14134,plain,(
    ! [A_4] : r2_hidden(A_4,k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_14131])).

tff(c_14771,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14745,c_14134])).

tff(c_112,plain,(
    ! [B_68,A_67] :
      ( k1_tarski(k1_funct_1(B_68,A_67)) = k11_relat_1(B_68,A_67)
      | ~ r2_hidden(A_67,k1_relat_1(B_68))
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_14786,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_14771,c_112])).

tff(c_14789,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_130,c_490,c_14786])).

tff(c_9440,plain,(
    ! [A_1595,B_1596,C_1597,D_1598] :
      ( k7_relset_1(A_1595,B_1596,C_1597,D_1598) = k9_relat_1(C_1597,D_1598)
      | ~ m1_subset_1(C_1597,k1_zfmisc_1(k2_zfmisc_1(A_1595,B_1596))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_9451,plain,(
    ! [D_1598] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_1598) = k9_relat_1('#skF_6',D_1598) ),
    inference(resolution,[status(thm)],[c_126,c_9440])).

tff(c_122,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_9452,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9451,c_122])).

tff(c_14790,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14789,c_9452])).

tff(c_14815,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_14790])).

tff(c_14819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_14815])).

tff(c_14820,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_14011])).

tff(c_92,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(A_48,k1_zfmisc_1(B_49))
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    ! [A_34] : k2_zfmisc_1(A_34,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_511,plain,(
    ! [C_142,A_143] :
      ( v4_relat_1(C_142,A_143)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_424])).

tff(c_515,plain,(
    ! [A_48,A_143] :
      ( v4_relat_1(A_48,A_143)
      | ~ r1_tarski(A_48,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_92,c_511])).

tff(c_100,plain,(
    ! [B_57,A_56] :
      ( r1_tarski(k1_relat_1(B_57),A_56)
      | ~ v4_relat_1(B_57,A_56)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_13847,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_13827])).

tff(c_13928,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_13847])).

tff(c_13931,plain,
    ( ~ v4_relat_1('#skF_6',k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_13928])).

tff(c_13934,plain,(
    ~ v4_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_13931])).

tff(c_13971,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_515,c_13934])).

tff(c_158,plain,(
    ! [A_84,B_85] : v1_relat_1(k2_zfmisc_1(A_84,B_85)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_160,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_158])).

tff(c_527,plain,(
    ! [A_154,A_155,B_156] :
      ( v4_relat_1(A_154,A_155)
      | ~ r1_tarski(A_154,k2_zfmisc_1(A_155,B_156)) ) ),
    inference(resolution,[status(thm)],[c_92,c_424])).

tff(c_555,plain,(
    ! [A_165] : v4_relat_1(k1_xboole_0,A_165) ),
    inference(resolution,[status(thm)],[c_8,c_527])).

tff(c_237,plain,(
    ! [B_100,A_101] :
      ( B_100 = A_101
      | ~ r1_tarski(B_100,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_249,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_237])).

tff(c_304,plain,(
    ! [B_107] :
      ( k1_relat_1(B_107) = k1_xboole_0
      | ~ v4_relat_1(B_107,k1_xboole_0)
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_289,c_249])).

tff(c_562,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_555,c_304])).

tff(c_568,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_562])).

tff(c_16963,plain,(
    ! [B_2820,B_2821] :
      ( k1_tarski(B_2820) = k1_relat_1(B_2821)
      | k1_relat_1(B_2821) = k1_xboole_0
      | ~ v4_relat_1(B_2821,k1_tarski(B_2820))
      | ~ v1_relat_1(B_2821) ) ),
    inference(resolution,[status(thm)],[c_289,c_24])).

tff(c_16993,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_439,c_16963])).

tff(c_17006,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_16993])).

tff(c_17007,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_17006])).

tff(c_16200,plain,(
    ! [B_2769,B_2770] :
      ( k1_tarski(B_2769) = k1_relat_1(B_2770)
      | k1_relat_1(B_2770) = k1_xboole_0
      | ~ v4_relat_1(B_2770,k1_tarski(B_2769))
      | ~ v1_relat_1(B_2770) ) ),
    inference(resolution,[status(thm)],[c_289,c_24])).

tff(c_16230,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_439,c_16200])).

tff(c_16243,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_16230])).

tff(c_16245,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_16243])).

tff(c_120,plain,(
    ! [D_79,B_77,C_78,A_76] :
      ( m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(B_77,C_78)))
      | ~ r1_tarski(k1_relat_1(D_79),B_77)
      | ~ m1_subset_1(D_79,k1_zfmisc_1(k2_zfmisc_1(A_76,C_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_15245,plain,(
    ! [D_2691,B_2692] :
      ( m1_subset_1(D_2691,k1_zfmisc_1(k2_zfmisc_1(B_2692,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(D_2691),B_2692)
      | ~ m1_subset_1(D_2691,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14820,c_120])).

tff(c_15664,plain,(
    ! [D_2753,B_2754] :
      ( r1_tarski(D_2753,k2_zfmisc_1(B_2754,'#skF_4'))
      | ~ r1_tarski(k1_relat_1(D_2753),B_2754)
      | ~ m1_subset_1(D_2753,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_15245,c_90])).

tff(c_15797,plain,(
    ! [D_2756] :
      ( r1_tarski(D_2756,k2_zfmisc_1(k1_relat_1(D_2756),'#skF_4'))
      | ~ m1_subset_1(D_2756,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6,c_15664])).

tff(c_116,plain,(
    ! [C_71,A_69,B_70] :
      ( v4_relat_1(C_71,A_69)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_13850,plain,(
    ! [B_2238] :
      ( v4_relat_1('#skF_6',B_2238)
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_2238) ) ),
    inference(resolution,[status(thm)],[c_13827,c_116])).

tff(c_15845,plain,
    ( v4_relat_1('#skF_6',k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')),'#skF_4'))
    | ~ m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_15797,c_13850])).

tff(c_16023,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_15845])).

tff(c_16027,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_16023])).

tff(c_16246,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16245,c_16027])).

tff(c_16270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16246])).

tff(c_16271,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_16243])).

tff(c_184,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_126,c_90])).

tff(c_244,plain,
    ( k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_184,c_237])).

tff(c_320,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_16278,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16271,c_320])).

tff(c_16289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14820,c_16278])).

tff(c_16291,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_15845])).

tff(c_13856,plain,(
    ! [B_2238] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(B_2238,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_2238) ) ),
    inference(resolution,[status(thm)],[c_13827,c_90])).

tff(c_15844,plain,
    ( r1_tarski('#skF_6',k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')),'#skF_4'),'#skF_4'))
    | ~ m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_15797,c_13856])).

tff(c_16678,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')),'#skF_4'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16291,c_15844])).

tff(c_17012,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),'#skF_4'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17007,c_16678])).

tff(c_17049,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_568,c_17012])).

tff(c_17051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13971,c_17049])).

tff(c_17052,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_17006])).

tff(c_17059,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17052,c_320])).

tff(c_17070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14820,c_17059])).

tff(c_17071,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_13847])).

tff(c_17088,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_17071,c_90])).

tff(c_17177,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_17088,c_249])).

tff(c_17213,plain,(
    ! [A_3] : r1_tarski('#skF_6',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17177,c_8])).

tff(c_108,plain,(
    ! [A_64] : k9_relat_1(k1_xboole_0,A_64) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_17209,plain,(
    ! [A_64] : k9_relat_1('#skF_6',A_64) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17177,c_17177,c_108])).

tff(c_17428,plain,(
    ~ r1_tarski('#skF_6',k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17209,c_9452])).

tff(c_17432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17213,c_17428])).

tff(c_17433,plain,(
    k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_17533,plain,(
    ! [C_2856,A_2857,B_2858] :
      ( v4_relat_1(C_2856,A_2857)
      | ~ m1_subset_1(C_2856,k1_zfmisc_1(k2_zfmisc_1(A_2857,B_2858))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_17559,plain,(
    ! [A_2863,A_2864,B_2865] :
      ( v4_relat_1(A_2863,A_2864)
      | ~ r1_tarski(A_2863,k2_zfmisc_1(A_2864,B_2865)) ) ),
    inference(resolution,[status(thm)],[c_92,c_17533])).

tff(c_17616,plain,(
    ! [A_2869,B_2870] : v4_relat_1(k2_zfmisc_1(A_2869,B_2870),A_2869) ),
    inference(resolution,[status(thm)],[c_6,c_17559])).

tff(c_17623,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17433,c_17616])).

tff(c_17711,plain,(
    ! [B_2884,A_2885] :
      ( k7_relat_1(B_2884,A_2885) = B_2884
      | ~ v4_relat_1(B_2884,A_2885)
      | ~ v1_relat_1(B_2884) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_17723,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_17623,c_17711])).

tff(c_17738,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_17723])).

tff(c_17799,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_17738,c_106])).

tff(c_17809,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_17799])).

tff(c_96,plain,(
    ! [A_53,B_55] :
      ( k9_relat_1(A_53,k1_tarski(B_55)) = k11_relat_1(A_53,B_55)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_17817,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_17809,c_96])).

tff(c_17827,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_17817])).

tff(c_124,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_30,plain,(
    ! [B_35,A_34] :
      ( k1_xboole_0 = B_35
      | k1_xboole_0 = A_34
      | k2_zfmisc_1(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_17441,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_17433,c_30])).

tff(c_17446,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_17441])).

tff(c_17475,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_17446])).

tff(c_17436,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17433,c_126])).

tff(c_18759,plain,(
    ! [B_3060,B_3061] :
      ( k1_tarski(B_3060) = k1_relat_1(B_3061)
      | k1_relat_1(B_3061) = k1_xboole_0
      | ~ v4_relat_1(B_3061,k1_tarski(B_3060))
      | ~ v1_relat_1(B_3061) ) ),
    inference(resolution,[status(thm)],[c_289,c_24])).

tff(c_18786,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_17623,c_18759])).

tff(c_18808,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_18786])).

tff(c_18848,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_18808])).

tff(c_18693,plain,(
    ! [D_3050,B_3051,C_3052,A_3053] :
      ( m1_subset_1(D_3050,k1_zfmisc_1(k2_zfmisc_1(B_3051,C_3052)))
      | ~ r1_tarski(k1_relat_1(D_3050),B_3051)
      | ~ m1_subset_1(D_3050,k1_zfmisc_1(k2_zfmisc_1(A_3053,C_3052))) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_18816,plain,(
    ! [D_3062,B_3063] :
      ( m1_subset_1(D_3062,k1_zfmisc_1(k2_zfmisc_1(B_3063,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(D_3062),B_3063)
      | ~ m1_subset_1(D_3062,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17433,c_18693])).

tff(c_19322,plain,(
    ! [D_3139] :
      ( m1_subset_1(D_3139,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(D_3139),k1_xboole_0)
      | ~ m1_subset_1(D_3139,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_18816])).

tff(c_19325,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18848,c_19322])).

tff(c_19337,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17436,c_6,c_19325])).

tff(c_19367,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_19337,c_90])).

tff(c_19381,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_19367,c_249])).

tff(c_19400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17475,c_19381])).

tff(c_19401,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_18808])).

tff(c_19438,plain,(
    ! [B_3146,D_3141,C_3144,A_3143,F_3145,G_3142,E_3147] : k6_enumset1(A_3143,A_3143,B_3146,C_3144,D_3141,E_3147,F_3145,G_3142) = k5_enumset1(A_3143,B_3146,C_3144,D_3141,E_3147,F_3145,G_3142) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    ! [F_41,G_42,D_39,A_36,J_47,E_40,H_43,C_38] : r2_hidden(J_47,k6_enumset1(A_36,J_47,C_38,D_39,E_40,F_41,G_42,H_43)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_19791,plain,(
    ! [C_3179,F_3176,D_3173,B_3174,A_3178,E_3177,G_3175] : r2_hidden(A_3178,k5_enumset1(A_3178,B_3174,C_3179,D_3173,E_3177,F_3176,G_3175)) ),
    inference(superposition,[status(thm),theory(equality)],[c_19438,c_50])).

tff(c_19795,plain,(
    ! [E_3181,F_3184,A_3183,D_3185,B_3182,C_3180] : r2_hidden(A_3183,k4_enumset1(A_3183,B_3182,C_3180,D_3185,E_3181,F_3184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_19791])).

tff(c_19799,plain,(
    ! [D_3187,B_3189,E_3186,C_3188,A_3190] : r2_hidden(A_3190,k3_enumset1(A_3190,B_3189,C_3188,D_3187,E_3186)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_19795])).

tff(c_19803,plain,(
    ! [A_3191,B_3192,C_3193,D_3194] : r2_hidden(A_3191,k2_enumset1(A_3191,B_3192,C_3193,D_3194)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_19799])).

tff(c_19807,plain,(
    ! [A_3195,B_3196,C_3197] : r2_hidden(A_3195,k1_enumset1(A_3195,B_3196,C_3197)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_19803])).

tff(c_19812,plain,(
    ! [A_3207,B_3208] : r2_hidden(A_3207,k2_tarski(A_3207,B_3208)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_19807])).

tff(c_19816,plain,(
    ! [A_3209] : r2_hidden(A_3209,k1_tarski(A_3209)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_19812])).

tff(c_19819,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_19401,c_19816])).

tff(c_19822,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_19819,c_112])).

tff(c_19825,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_130,c_17827,c_19822])).

tff(c_18338,plain,(
    ! [A_3004,B_3005,C_3006,D_3007] :
      ( k7_relset_1(A_3004,B_3005,C_3006,D_3007) = k9_relat_1(C_3006,D_3007)
      | ~ m1_subset_1(C_3006,k1_zfmisc_1(k2_zfmisc_1(A_3004,B_3005))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_18362,plain,(
    ! [C_3009,D_3010] :
      ( k7_relset_1(k1_tarski('#skF_3'),'#skF_4',C_3009,D_3010) = k9_relat_1(C_3009,D_3010)
      | ~ m1_subset_1(C_3009,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17433,c_18338])).

tff(c_18368,plain,(
    ! [D_3010] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_3010) = k9_relat_1('#skF_6',D_3010) ),
    inference(resolution,[status(thm)],[c_17436,c_18362])).

tff(c_18370,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18368,c_122])).

tff(c_19826,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19825,c_18370])).

tff(c_19851,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_104,c_19826])).

tff(c_19855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_19851])).

tff(c_19857,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_17446])).

tff(c_19866,plain,(
    ! [A_3] : r1_tarski('#skF_6',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19857,c_8])).

tff(c_19862,plain,(
    ! [A_64] : k9_relat_1('#skF_6',A_64) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19857,c_19857,c_108])).

tff(c_19865,plain,(
    ! [B_35] : k2_zfmisc_1('#skF_6',B_35) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19857,c_19857,c_34])).

tff(c_20877,plain,(
    ! [A_3386,B_3387,C_3388,D_3389] :
      ( k7_relset_1(A_3386,B_3387,C_3388,D_3389) = k9_relat_1(C_3388,D_3389)
      | ~ m1_subset_1(C_3388,k1_zfmisc_1(k2_zfmisc_1(A_3386,B_3387))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_21095,plain,(
    ! [B_3413,C_3414,D_3415] :
      ( k7_relset_1('#skF_6',B_3413,C_3414,D_3415) = k9_relat_1(C_3414,D_3415)
      | ~ m1_subset_1(C_3414,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19865,c_20877])).

tff(c_21097,plain,(
    ! [B_3413,D_3415] : k7_relset_1('#skF_6',B_3413,'#skF_6',D_3415) = k9_relat_1('#skF_6',D_3415) ),
    inference(resolution,[status(thm)],[c_17436,c_21095])).

tff(c_21102,plain,(
    ! [B_3413,D_3415] : k7_relset_1('#skF_6',B_3413,'#skF_6',D_3415) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19862,c_21097])).

tff(c_19856,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_17446])).

tff(c_19873,plain,(
    k1_tarski('#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19857,c_19856])).

tff(c_19875,plain,(
    ~ r1_tarski(k7_relset_1('#skF_6','#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19873,c_122])).

tff(c_21104,plain,(
    ~ r1_tarski('#skF_6',k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21102,c_19875])).

tff(c_21107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19866,c_21104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.06/4.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.06/4.75  
% 12.06/4.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.06/4.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 12.06/4.75  
% 12.06/4.75  %Foreground sorts:
% 12.06/4.75  
% 12.06/4.75  
% 12.06/4.75  %Background operators:
% 12.06/4.75  
% 12.06/4.75  
% 12.06/4.75  %Foreground operators:
% 12.06/4.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.06/4.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.06/4.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.06/4.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.06/4.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.06/4.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.06/4.75  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.06/4.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.06/4.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.06/4.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.06/4.75  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 12.06/4.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.06/4.75  tff('#skF_5', type, '#skF_5': $i).
% 12.06/4.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.06/4.75  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 12.06/4.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.06/4.75  tff('#skF_6', type, '#skF_6': $i).
% 12.06/4.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.06/4.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.06/4.75  tff('#skF_3', type, '#skF_3': $i).
% 12.06/4.75  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.06/4.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.06/4.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.06/4.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.06/4.75  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.06/4.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.06/4.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.06/4.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.06/4.75  tff('#skF_4', type, '#skF_4': $i).
% 12.06/4.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.06/4.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.06/4.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.06/4.75  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.06/4.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.06/4.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.06/4.75  
% 12.41/4.78  tff(f_113, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.41/4.78  tff(f_165, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 12.41/4.78  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.41/4.78  tff(f_117, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 12.41/4.78  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.41/4.78  tff(f_105, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 12.41/4.78  tff(f_143, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.41/4.78  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 12.41/4.78  tff(f_121, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 12.41/4.78  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.41/4.78  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.41/4.78  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 12.41/4.78  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 12.41/4.78  tff(f_153, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 12.41/4.78  tff(f_93, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.41/4.78  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 12.41/4.78  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 12.41/4.78  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 12.41/4.78  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 12.41/4.78  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 12.41/4.78  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 12.41/4.78  tff(f_47, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 12.41/4.78  tff(f_89, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 12.41/4.78  tff(f_137, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 12.41/4.78  tff(f_147, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 12.41/4.78  tff(f_123, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 12.41/4.78  tff(c_102, plain, (![A_58, B_59]: (v1_relat_1(k2_zfmisc_1(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 12.41/4.78  tff(c_126, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.41/4.78  tff(c_199, plain, (![B_94, A_95]: (v1_relat_1(B_94) | ~m1_subset_1(B_94, k1_zfmisc_1(A_95)) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_100])).
% 12.41/4.78  tff(c_205, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_126, c_199])).
% 12.41/4.78  tff(c_209, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_205])).
% 12.41/4.78  tff(c_104, plain, (![B_61, A_60]: (r1_tarski(k9_relat_1(B_61, A_60), k2_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_117])).
% 12.41/4.78  tff(c_130, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.41/4.78  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.41/4.78  tff(c_464, plain, (![A_139, B_140]: (k9_relat_1(A_139, k1_tarski(B_140))=k11_relat_1(A_139, B_140) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.41/4.78  tff(c_424, plain, (![C_136, A_137, B_138]: (v4_relat_1(C_136, A_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 12.41/4.78  tff(c_439, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_126, c_424])).
% 12.41/4.78  tff(c_110, plain, (![B_66, A_65]: (k7_relat_1(B_66, A_65)=B_66 | ~v4_relat_1(B_66, A_65) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.41/4.78  tff(c_442, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_439, c_110])).
% 12.41/4.78  tff(c_445, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_209, c_442])).
% 12.41/4.78  tff(c_106, plain, (![B_63, A_62]: (k2_relat_1(k7_relat_1(B_63, A_62))=k9_relat_1(B_63, A_62) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.41/4.78  tff(c_449, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_445, c_106])).
% 12.41/4.78  tff(c_453, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_449])).
% 12.41/4.78  tff(c_470, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_464, c_453])).
% 12.41/4.78  tff(c_490, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_470])).
% 12.41/4.78  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.41/4.78  tff(c_34, plain, (![B_35]: (k2_zfmisc_1(k1_xboole_0, B_35)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.41/4.78  tff(c_289, plain, (![B_107, A_108]: (r1_tarski(k1_relat_1(B_107), A_108) | ~v4_relat_1(B_107, A_108) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.41/4.78  tff(c_24, plain, (![B_33, A_32]: (k1_tarski(B_33)=A_32 | k1_xboole_0=A_32 | ~r1_tarski(A_32, k1_tarski(B_33)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.41/4.78  tff(c_14684, plain, (![B_2534, B_2535]: (k1_tarski(B_2534)=k1_relat_1(B_2535) | k1_relat_1(B_2535)=k1_xboole_0 | ~v4_relat_1(B_2535, k1_tarski(B_2534)) | ~v1_relat_1(B_2535))), inference(resolution, [status(thm)], [c_289, c_24])).
% 12.41/4.78  tff(c_14714, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_439, c_14684])).
% 12.41/4.78  tff(c_14727, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_209, c_14714])).
% 12.41/4.78  tff(c_14728, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14727])).
% 12.41/4.78  tff(c_13799, plain, (![D_2233, B_2234, C_2235, A_2236]: (m1_subset_1(D_2233, k1_zfmisc_1(k2_zfmisc_1(B_2234, C_2235))) | ~r1_tarski(k1_relat_1(D_2233), B_2234) | ~m1_subset_1(D_2233, k1_zfmisc_1(k2_zfmisc_1(A_2236, C_2235))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.41/4.78  tff(c_13827, plain, (![B_2238]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_2238, '#skF_4'))) | ~r1_tarski(k1_relat_1('#skF_6'), B_2238))), inference(resolution, [status(thm)], [c_126, c_13799])).
% 12.41/4.78  tff(c_90, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.41/4.78  tff(c_13972, plain, (![B_2247]: (r1_tarski('#skF_6', k2_zfmisc_1(B_2247, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_6'), B_2247))), inference(resolution, [status(thm)], [c_13827, c_90])).
% 12.41/4.78  tff(c_13984, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_13972])).
% 12.41/4.78  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.41/4.78  tff(c_14011, plain, (k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_13984, c_2])).
% 12.41/4.78  tff(c_14162, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_14011])).
% 12.41/4.78  tff(c_14730, plain, (~r1_tarski(k2_zfmisc_1(k1_xboole_0, '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14728, c_14162])).
% 12.41/4.78  tff(c_14744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_34, c_14730])).
% 12.41/4.78  tff(c_14745, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_14727])).
% 12.41/4.78  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.41/4.78  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.41/4.78  tff(c_14, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.41/4.78  tff(c_16, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.41/4.78  tff(c_18, plain, (![E_18, C_16, D_17, A_14, B_15]: (k4_enumset1(A_14, A_14, B_15, C_16, D_17, E_18)=k3_enumset1(A_14, B_15, C_16, D_17, E_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.41/4.78  tff(c_20, plain, (![A_19, C_21, D_22, B_20, F_24, E_23]: (k5_enumset1(A_19, A_19, B_20, C_21, D_22, E_23, F_24)=k4_enumset1(A_19, B_20, C_21, D_22, E_23, F_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.41/4.78  tff(c_13935, plain, (![G_2241, C_2243, D_2240, A_2242, B_2245, F_2244, E_2246]: (k6_enumset1(A_2242, A_2242, B_2245, C_2243, D_2240, E_2246, F_2244, G_2241)=k5_enumset1(A_2242, B_2245, C_2243, D_2240, E_2246, F_2244, G_2241))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.41/4.78  tff(c_44, plain, (![F_41, G_42, D_39, A_36, J_47, H_43, C_38, B_37]: (r2_hidden(J_47, k6_enumset1(A_36, B_37, C_38, D_39, J_47, F_41, G_42, H_43)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.41/4.78  tff(c_14048, plain, (![E_2252, A_2255, D_2256, B_2258, G_2254, C_2257, F_2253]: (r2_hidden(D_2256, k5_enumset1(A_2255, B_2258, C_2257, D_2256, E_2252, F_2253, G_2254)))), inference(superposition, [status(thm), theory('equality')], [c_13935, c_44])).
% 12.41/4.78  tff(c_14052, plain, (![A_2262, B_2261, E_2260, C_2259, F_2263, D_2264]: (r2_hidden(C_2259, k4_enumset1(A_2262, B_2261, C_2259, D_2264, E_2260, F_2263)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_14048])).
% 12.41/4.78  tff(c_14100, plain, (![C_2276, E_2274, A_2278, B_2277, D_2275]: (r2_hidden(B_2277, k3_enumset1(A_2278, B_2277, C_2276, D_2275, E_2274)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_14052])).
% 12.41/4.78  tff(c_14104, plain, (![A_2279, B_2280, C_2281, D_2282]: (r2_hidden(A_2279, k2_enumset1(A_2279, B_2280, C_2281, D_2282)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_14100])).
% 12.41/4.78  tff(c_14108, plain, (![A_2283, B_2284, C_2285]: (r2_hidden(A_2283, k1_enumset1(A_2283, B_2284, C_2285)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_14104])).
% 12.41/4.78  tff(c_14131, plain, (![A_2288, B_2289]: (r2_hidden(A_2288, k2_tarski(A_2288, B_2289)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_14108])).
% 12.41/4.78  tff(c_14134, plain, (![A_4]: (r2_hidden(A_4, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_14131])).
% 12.41/4.78  tff(c_14771, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_14745, c_14134])).
% 12.41/4.78  tff(c_112, plain, (![B_68, A_67]: (k1_tarski(k1_funct_1(B_68, A_67))=k11_relat_1(B_68, A_67) | ~r2_hidden(A_67, k1_relat_1(B_68)) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_137])).
% 12.41/4.78  tff(c_14786, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_14771, c_112])).
% 12.41/4.78  tff(c_14789, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_130, c_490, c_14786])).
% 12.41/4.78  tff(c_9440, plain, (![A_1595, B_1596, C_1597, D_1598]: (k7_relset_1(A_1595, B_1596, C_1597, D_1598)=k9_relat_1(C_1597, D_1598) | ~m1_subset_1(C_1597, k1_zfmisc_1(k2_zfmisc_1(A_1595, B_1596))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 12.41/4.78  tff(c_9451, plain, (![D_1598]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_1598)=k9_relat_1('#skF_6', D_1598))), inference(resolution, [status(thm)], [c_126, c_9440])).
% 12.41/4.78  tff(c_122, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.41/4.78  tff(c_9452, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9451, c_122])).
% 12.41/4.78  tff(c_14790, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_14789, c_9452])).
% 12.41/4.78  tff(c_14815, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_104, c_14790])).
% 12.41/4.78  tff(c_14819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_14815])).
% 12.41/4.78  tff(c_14820, plain, (k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_14011])).
% 12.41/4.78  tff(c_92, plain, (![A_48, B_49]: (m1_subset_1(A_48, k1_zfmisc_1(B_49)) | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.41/4.78  tff(c_32, plain, (![A_34]: (k2_zfmisc_1(A_34, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.41/4.78  tff(c_511, plain, (![C_142, A_143]: (v4_relat_1(C_142, A_143) | ~m1_subset_1(C_142, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_424])).
% 12.41/4.78  tff(c_515, plain, (![A_48, A_143]: (v4_relat_1(A_48, A_143) | ~r1_tarski(A_48, k1_xboole_0))), inference(resolution, [status(thm)], [c_92, c_511])).
% 12.41/4.78  tff(c_100, plain, (![B_57, A_56]: (r1_tarski(k1_relat_1(B_57), A_56) | ~v4_relat_1(B_57, A_56) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_111])).
% 12.41/4.78  tff(c_13847, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_13827])).
% 12.41/4.78  tff(c_13928, plain, (~r1_tarski(k1_relat_1('#skF_6'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_13847])).
% 12.41/4.78  tff(c_13931, plain, (~v4_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_100, c_13928])).
% 12.41/4.78  tff(c_13934, plain, (~v4_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_209, c_13931])).
% 12.41/4.78  tff(c_13971, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_515, c_13934])).
% 12.41/4.78  tff(c_158, plain, (![A_84, B_85]: (v1_relat_1(k2_zfmisc_1(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 12.41/4.78  tff(c_160, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_158])).
% 12.41/4.78  tff(c_527, plain, (![A_154, A_155, B_156]: (v4_relat_1(A_154, A_155) | ~r1_tarski(A_154, k2_zfmisc_1(A_155, B_156)))), inference(resolution, [status(thm)], [c_92, c_424])).
% 12.41/4.78  tff(c_555, plain, (![A_165]: (v4_relat_1(k1_xboole_0, A_165))), inference(resolution, [status(thm)], [c_8, c_527])).
% 12.41/4.78  tff(c_237, plain, (![B_100, A_101]: (B_100=A_101 | ~r1_tarski(B_100, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.41/4.78  tff(c_249, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_237])).
% 12.41/4.78  tff(c_304, plain, (![B_107]: (k1_relat_1(B_107)=k1_xboole_0 | ~v4_relat_1(B_107, k1_xboole_0) | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_289, c_249])).
% 12.41/4.78  tff(c_562, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_555, c_304])).
% 12.41/4.78  tff(c_568, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_160, c_562])).
% 12.41/4.78  tff(c_16963, plain, (![B_2820, B_2821]: (k1_tarski(B_2820)=k1_relat_1(B_2821) | k1_relat_1(B_2821)=k1_xboole_0 | ~v4_relat_1(B_2821, k1_tarski(B_2820)) | ~v1_relat_1(B_2821))), inference(resolution, [status(thm)], [c_289, c_24])).
% 12.41/4.78  tff(c_16993, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_439, c_16963])).
% 12.41/4.78  tff(c_17006, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_209, c_16993])).
% 12.41/4.78  tff(c_17007, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_17006])).
% 12.41/4.78  tff(c_16200, plain, (![B_2769, B_2770]: (k1_tarski(B_2769)=k1_relat_1(B_2770) | k1_relat_1(B_2770)=k1_xboole_0 | ~v4_relat_1(B_2770, k1_tarski(B_2769)) | ~v1_relat_1(B_2770))), inference(resolution, [status(thm)], [c_289, c_24])).
% 12.41/4.78  tff(c_16230, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_439, c_16200])).
% 12.41/4.78  tff(c_16243, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_209, c_16230])).
% 12.41/4.78  tff(c_16245, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_16243])).
% 12.41/4.78  tff(c_120, plain, (![D_79, B_77, C_78, A_76]: (m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(B_77, C_78))) | ~r1_tarski(k1_relat_1(D_79), B_77) | ~m1_subset_1(D_79, k1_zfmisc_1(k2_zfmisc_1(A_76, C_78))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.41/4.78  tff(c_15245, plain, (![D_2691, B_2692]: (m1_subset_1(D_2691, k1_zfmisc_1(k2_zfmisc_1(B_2692, '#skF_4'))) | ~r1_tarski(k1_relat_1(D_2691), B_2692) | ~m1_subset_1(D_2691, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_14820, c_120])).
% 12.41/4.78  tff(c_15664, plain, (![D_2753, B_2754]: (r1_tarski(D_2753, k2_zfmisc_1(B_2754, '#skF_4')) | ~r1_tarski(k1_relat_1(D_2753), B_2754) | ~m1_subset_1(D_2753, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_15245, c_90])).
% 12.41/4.78  tff(c_15797, plain, (![D_2756]: (r1_tarski(D_2756, k2_zfmisc_1(k1_relat_1(D_2756), '#skF_4')) | ~m1_subset_1(D_2756, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_6, c_15664])).
% 12.41/4.78  tff(c_116, plain, (![C_71, A_69, B_70]: (v4_relat_1(C_71, A_69) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 12.41/4.78  tff(c_13850, plain, (![B_2238]: (v4_relat_1('#skF_6', B_2238) | ~r1_tarski(k1_relat_1('#skF_6'), B_2238))), inference(resolution, [status(thm)], [c_13827, c_116])).
% 12.41/4.78  tff(c_15845, plain, (v4_relat_1('#skF_6', k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')), '#skF_4')) | ~m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_15797, c_13850])).
% 12.41/4.78  tff(c_16023, plain, (~m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_15845])).
% 12.41/4.78  tff(c_16027, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_92, c_16023])).
% 12.41/4.78  tff(c_16246, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16245, c_16027])).
% 12.41/4.78  tff(c_16270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_16246])).
% 12.41/4.78  tff(c_16271, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_16243])).
% 12.41/4.78  tff(c_184, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_126, c_90])).
% 12.41/4.78  tff(c_244, plain, (k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_184, c_237])).
% 12.41/4.78  tff(c_320, plain, (~r1_tarski(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_244])).
% 12.41/4.78  tff(c_16278, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16271, c_320])).
% 12.41/4.78  tff(c_16289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14820, c_16278])).
% 12.41/4.78  tff(c_16291, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_15845])).
% 12.41/4.78  tff(c_13856, plain, (![B_2238]: (r1_tarski('#skF_6', k2_zfmisc_1(B_2238, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_6'), B_2238))), inference(resolution, [status(thm)], [c_13827, c_90])).
% 12.41/4.78  tff(c_15844, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')), '#skF_4'), '#skF_4')) | ~m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_15797, c_13856])).
% 12.41/4.78  tff(c_16678, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')), '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16291, c_15844])).
% 12.41/4.78  tff(c_17012, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0), '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17007, c_16678])).
% 12.41/4.78  tff(c_17049, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_568, c_17012])).
% 12.41/4.78  tff(c_17051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13971, c_17049])).
% 12.41/4.78  tff(c_17052, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_17006])).
% 12.41/4.78  tff(c_17059, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_17052, c_320])).
% 12.41/4.78  tff(c_17070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_14820, c_17059])).
% 12.41/4.78  tff(c_17071, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_13847])).
% 12.41/4.78  tff(c_17088, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_17071, c_90])).
% 12.41/4.78  tff(c_17177, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_17088, c_249])).
% 12.41/4.78  tff(c_17213, plain, (![A_3]: (r1_tarski('#skF_6', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_17177, c_8])).
% 12.41/4.78  tff(c_108, plain, (![A_64]: (k9_relat_1(k1_xboole_0, A_64)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_123])).
% 12.41/4.78  tff(c_17209, plain, (![A_64]: (k9_relat_1('#skF_6', A_64)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_17177, c_17177, c_108])).
% 12.41/4.78  tff(c_17428, plain, (~r1_tarski('#skF_6', k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_17209, c_9452])).
% 12.41/4.78  tff(c_17432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17213, c_17428])).
% 12.41/4.78  tff(c_17433, plain, (k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_244])).
% 12.41/4.78  tff(c_17533, plain, (![C_2856, A_2857, B_2858]: (v4_relat_1(C_2856, A_2857) | ~m1_subset_1(C_2856, k1_zfmisc_1(k2_zfmisc_1(A_2857, B_2858))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 12.41/4.78  tff(c_17559, plain, (![A_2863, A_2864, B_2865]: (v4_relat_1(A_2863, A_2864) | ~r1_tarski(A_2863, k2_zfmisc_1(A_2864, B_2865)))), inference(resolution, [status(thm)], [c_92, c_17533])).
% 12.41/4.78  tff(c_17616, plain, (![A_2869, B_2870]: (v4_relat_1(k2_zfmisc_1(A_2869, B_2870), A_2869))), inference(resolution, [status(thm)], [c_6, c_17559])).
% 12.41/4.78  tff(c_17623, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_17433, c_17616])).
% 12.41/4.78  tff(c_17711, plain, (![B_2884, A_2885]: (k7_relat_1(B_2884, A_2885)=B_2884 | ~v4_relat_1(B_2884, A_2885) | ~v1_relat_1(B_2884))), inference(cnfTransformation, [status(thm)], [f_129])).
% 12.41/4.78  tff(c_17723, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_17623, c_17711])).
% 12.41/4.78  tff(c_17738, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_209, c_17723])).
% 12.41/4.78  tff(c_17799, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_17738, c_106])).
% 12.41/4.78  tff(c_17809, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_17799])).
% 12.41/4.78  tff(c_96, plain, (![A_53, B_55]: (k9_relat_1(A_53, k1_tarski(B_55))=k11_relat_1(A_53, B_55) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_105])).
% 12.41/4.78  tff(c_17817, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_17809, c_96])).
% 12.41/4.78  tff(c_17827, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_17817])).
% 12.41/4.78  tff(c_124, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.41/4.78  tff(c_30, plain, (![B_35, A_34]: (k1_xboole_0=B_35 | k1_xboole_0=A_34 | k2_zfmisc_1(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.41/4.78  tff(c_17441, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_17433, c_30])).
% 12.41/4.78  tff(c_17446, plain, (k1_tarski('#skF_3')=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_124, c_17441])).
% 12.41/4.78  tff(c_17475, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_17446])).
% 12.41/4.78  tff(c_17436, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_17433, c_126])).
% 12.41/4.78  tff(c_18759, plain, (![B_3060, B_3061]: (k1_tarski(B_3060)=k1_relat_1(B_3061) | k1_relat_1(B_3061)=k1_xboole_0 | ~v4_relat_1(B_3061, k1_tarski(B_3060)) | ~v1_relat_1(B_3061))), inference(resolution, [status(thm)], [c_289, c_24])).
% 12.41/4.78  tff(c_18786, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_17623, c_18759])).
% 12.41/4.78  tff(c_18808, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_209, c_18786])).
% 12.41/4.78  tff(c_18848, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_18808])).
% 12.41/4.78  tff(c_18693, plain, (![D_3050, B_3051, C_3052, A_3053]: (m1_subset_1(D_3050, k1_zfmisc_1(k2_zfmisc_1(B_3051, C_3052))) | ~r1_tarski(k1_relat_1(D_3050), B_3051) | ~m1_subset_1(D_3050, k1_zfmisc_1(k2_zfmisc_1(A_3053, C_3052))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 12.41/4.78  tff(c_18816, plain, (![D_3062, B_3063]: (m1_subset_1(D_3062, k1_zfmisc_1(k2_zfmisc_1(B_3063, '#skF_4'))) | ~r1_tarski(k1_relat_1(D_3062), B_3063) | ~m1_subset_1(D_3062, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_17433, c_18693])).
% 12.41/4.78  tff(c_19322, plain, (![D_3139]: (m1_subset_1(D_3139, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(D_3139), k1_xboole_0) | ~m1_subset_1(D_3139, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_18816])).
% 12.41/4.78  tff(c_19325, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_18848, c_19322])).
% 12.41/4.78  tff(c_19337, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_17436, c_6, c_19325])).
% 12.41/4.78  tff(c_19367, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_19337, c_90])).
% 12.41/4.78  tff(c_19381, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_19367, c_249])).
% 12.41/4.78  tff(c_19400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17475, c_19381])).
% 12.41/4.78  tff(c_19401, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_18808])).
% 12.41/4.78  tff(c_19438, plain, (![B_3146, D_3141, C_3144, A_3143, F_3145, G_3142, E_3147]: (k6_enumset1(A_3143, A_3143, B_3146, C_3144, D_3141, E_3147, F_3145, G_3142)=k5_enumset1(A_3143, B_3146, C_3144, D_3141, E_3147, F_3145, G_3142))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.41/4.78  tff(c_50, plain, (![F_41, G_42, D_39, A_36, J_47, E_40, H_43, C_38]: (r2_hidden(J_47, k6_enumset1(A_36, J_47, C_38, D_39, E_40, F_41, G_42, H_43)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.41/4.78  tff(c_19791, plain, (![C_3179, F_3176, D_3173, B_3174, A_3178, E_3177, G_3175]: (r2_hidden(A_3178, k5_enumset1(A_3178, B_3174, C_3179, D_3173, E_3177, F_3176, G_3175)))), inference(superposition, [status(thm), theory('equality')], [c_19438, c_50])).
% 12.41/4.78  tff(c_19795, plain, (![E_3181, F_3184, A_3183, D_3185, B_3182, C_3180]: (r2_hidden(A_3183, k4_enumset1(A_3183, B_3182, C_3180, D_3185, E_3181, F_3184)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_19791])).
% 12.41/4.78  tff(c_19799, plain, (![D_3187, B_3189, E_3186, C_3188, A_3190]: (r2_hidden(A_3190, k3_enumset1(A_3190, B_3189, C_3188, D_3187, E_3186)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_19795])).
% 12.41/4.78  tff(c_19803, plain, (![A_3191, B_3192, C_3193, D_3194]: (r2_hidden(A_3191, k2_enumset1(A_3191, B_3192, C_3193, D_3194)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_19799])).
% 12.41/4.78  tff(c_19807, plain, (![A_3195, B_3196, C_3197]: (r2_hidden(A_3195, k1_enumset1(A_3195, B_3196, C_3197)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_19803])).
% 12.41/4.78  tff(c_19812, plain, (![A_3207, B_3208]: (r2_hidden(A_3207, k2_tarski(A_3207, B_3208)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_19807])).
% 12.41/4.78  tff(c_19816, plain, (![A_3209]: (r2_hidden(A_3209, k1_tarski(A_3209)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_19812])).
% 12.41/4.78  tff(c_19819, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_19401, c_19816])).
% 12.41/4.78  tff(c_19822, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_19819, c_112])).
% 12.41/4.78  tff(c_19825, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_130, c_17827, c_19822])).
% 12.41/4.78  tff(c_18338, plain, (![A_3004, B_3005, C_3006, D_3007]: (k7_relset_1(A_3004, B_3005, C_3006, D_3007)=k9_relat_1(C_3006, D_3007) | ~m1_subset_1(C_3006, k1_zfmisc_1(k2_zfmisc_1(A_3004, B_3005))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 12.41/4.78  tff(c_18362, plain, (![C_3009, D_3010]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', C_3009, D_3010)=k9_relat_1(C_3009, D_3010) | ~m1_subset_1(C_3009, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_17433, c_18338])).
% 12.41/4.78  tff(c_18368, plain, (![D_3010]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_3010)=k9_relat_1('#skF_6', D_3010))), inference(resolution, [status(thm)], [c_17436, c_18362])).
% 12.41/4.78  tff(c_18370, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_18368, c_122])).
% 12.41/4.78  tff(c_19826, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_19825, c_18370])).
% 12.41/4.78  tff(c_19851, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_104, c_19826])).
% 12.41/4.78  tff(c_19855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_19851])).
% 12.41/4.78  tff(c_19857, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_17446])).
% 12.41/4.78  tff(c_19866, plain, (![A_3]: (r1_tarski('#skF_6', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_19857, c_8])).
% 12.41/4.78  tff(c_19862, plain, (![A_64]: (k9_relat_1('#skF_6', A_64)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19857, c_19857, c_108])).
% 12.41/4.78  tff(c_19865, plain, (![B_35]: (k2_zfmisc_1('#skF_6', B_35)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19857, c_19857, c_34])).
% 12.41/4.78  tff(c_20877, plain, (![A_3386, B_3387, C_3388, D_3389]: (k7_relset_1(A_3386, B_3387, C_3388, D_3389)=k9_relat_1(C_3388, D_3389) | ~m1_subset_1(C_3388, k1_zfmisc_1(k2_zfmisc_1(A_3386, B_3387))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 12.41/4.78  tff(c_21095, plain, (![B_3413, C_3414, D_3415]: (k7_relset_1('#skF_6', B_3413, C_3414, D_3415)=k9_relat_1(C_3414, D_3415) | ~m1_subset_1(C_3414, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_19865, c_20877])).
% 12.41/4.78  tff(c_21097, plain, (![B_3413, D_3415]: (k7_relset_1('#skF_6', B_3413, '#skF_6', D_3415)=k9_relat_1('#skF_6', D_3415))), inference(resolution, [status(thm)], [c_17436, c_21095])).
% 12.41/4.78  tff(c_21102, plain, (![B_3413, D_3415]: (k7_relset_1('#skF_6', B_3413, '#skF_6', D_3415)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19862, c_21097])).
% 12.41/4.78  tff(c_19856, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_17446])).
% 12.41/4.78  tff(c_19873, plain, (k1_tarski('#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_19857, c_19856])).
% 12.41/4.78  tff(c_19875, plain, (~r1_tarski(k7_relset_1('#skF_6', '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_19873, c_122])).
% 12.41/4.78  tff(c_21104, plain, (~r1_tarski('#skF_6', k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_21102, c_19875])).
% 12.41/4.78  tff(c_21107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19866, c_21104])).
% 12.41/4.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.41/4.78  
% 12.41/4.78  Inference rules
% 12.41/4.78  ----------------------
% 12.41/4.78  #Ref     : 0
% 12.41/4.78  #Sup     : 4349
% 12.41/4.78  #Fact    : 0
% 12.41/4.78  #Define  : 0
% 12.41/4.78  #Split   : 67
% 12.41/4.78  #Chain   : 0
% 12.41/4.78  #Close   : 0
% 12.41/4.78  
% 12.41/4.78  Ordering : KBO
% 12.41/4.78  
% 12.41/4.78  Simplification rules
% 12.41/4.78  ----------------------
% 12.41/4.78  #Subsume      : 700
% 12.41/4.78  #Demod        : 5003
% 12.41/4.78  #Tautology    : 2463
% 12.41/4.78  #SimpNegUnit  : 93
% 12.41/4.78  #BackRed      : 729
% 12.41/4.78  
% 12.41/4.78  #Partial instantiations: 0
% 12.41/4.78  #Strategies tried      : 1
% 12.41/4.78  
% 12.41/4.78  Timing (in seconds)
% 12.41/4.78  ----------------------
% 12.41/4.79  Preprocessing        : 0.41
% 12.41/4.79  Parsing              : 0.20
% 12.41/4.79  CNF conversion       : 0.03
% 12.41/4.79  Main loop            : 3.54
% 12.41/4.79  Inferencing          : 1.10
% 12.41/4.79  Reduction            : 1.33
% 12.41/4.79  Demodulation         : 1.02
% 12.41/4.79  BG Simplification    : 0.09
% 12.41/4.79  Subsumption          : 0.79
% 12.41/4.79  Abstraction          : 0.11
% 12.41/4.79  MUC search           : 0.00
% 12.41/4.79  Cooper               : 0.00
% 12.41/4.79  Total                : 4.02
% 12.41/4.79  Index Insertion      : 0.00
% 12.41/4.79  Index Deletion       : 0.00
% 12.41/4.79  Index Matching       : 0.00
% 12.41/4.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
