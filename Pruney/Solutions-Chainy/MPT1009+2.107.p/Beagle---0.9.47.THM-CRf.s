%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:57 EST 2020

% Result     : Theorem 8.32s
% Output     : CNFRefutation 8.60s
% Verified   : 
% Statistics : Number of formulae       :  361 (2196 expanded)
%              Number of leaves         :   59 ( 735 expanded)
%              Depth                    :   21
%              Number of atoms          :  568 (4833 expanded)
%              Number of equality atoms :  182 (1049 expanded)
%              Maximal formula depth    :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_159,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_147,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_117,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_90,plain,(
    ! [A_56,B_57] : v1_relat_1(k2_zfmisc_1(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_114,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_233,plain,(
    ! [B_99,A_100] :
      ( v1_relat_1(B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_100))
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_236,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_114,c_233])).

tff(c_242,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_236])).

tff(c_92,plain,(
    ! [B_59,A_58] :
      ( r1_tarski(k9_relat_1(B_59,A_58),k2_relat_1(B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_118,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_88,plain,(
    ! [B_55,A_54] :
      ( r1_tarski(k1_relat_1(B_55),A_54)
      | ~ v4_relat_1(B_55,A_54)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    ! [B_35] : k2_zfmisc_1(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_897,plain,(
    ! [D_275,B_276,C_277,A_278] :
      ( m1_subset_1(D_275,k1_zfmisc_1(k2_zfmisc_1(B_276,C_277)))
      | ~ r1_tarski(k1_relat_1(D_275),B_276)
      | ~ m1_subset_1(D_275,k1_zfmisc_1(k2_zfmisc_1(A_278,C_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_947,plain,(
    ! [B_283] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_283,'#skF_4')))
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_283) ) ),
    inference(resolution,[status(thm)],[c_114,c_897])).

tff(c_967,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_947])).

tff(c_1040,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_1056,plain,
    ( ~ v4_relat_1('#skF_6',k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_1040])).

tff(c_1059,plain,(
    ~ v4_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_1056])).

tff(c_277,plain,(
    ! [C_136,A_137,B_138] :
      ( v4_relat_1(C_136,A_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_291,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_114,c_277])).

tff(c_372,plain,(
    ! [B_155,A_156] :
      ( k7_relat_1(B_155,A_156) = B_155
      | ~ v4_relat_1(B_155,A_156)
      | ~ v1_relat_1(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_384,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_291,c_372])).

tff(c_397,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_384])).

tff(c_94,plain,(
    ! [B_61,A_60] :
      ( k2_relat_1(k7_relat_1(B_61,A_60)) = k9_relat_1(B_61,A_60)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_423,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_94])).

tff(c_427,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_423])).

tff(c_560,plain,(
    ! [A_166,B_167] :
      ( k9_relat_1(A_166,k1_tarski(B_167)) = k11_relat_1(A_166,B_167)
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_579,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_560])).

tff(c_591,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_579])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_624,plain,(
    ! [B_178,A_179] :
      ( k1_tarski(B_178) = A_179
      | k1_xboole_0 = A_179
      | ~ r1_tarski(A_179,k1_tarski(B_178)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1826,plain,(
    ! [B_419,B_420] :
      ( k1_tarski(B_419) = k1_relat_1(B_420)
      | k1_relat_1(B_420) = k1_xboole_0
      | ~ v4_relat_1(B_420,k1_tarski(B_419))
      | ~ v1_relat_1(B_420) ) ),
    inference(resolution,[status(thm)],[c_88,c_624])).

tff(c_1853,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_291,c_1826])).

tff(c_1866,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_1853])).

tff(c_1867,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1866])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1041,plain,(
    ! [B_292] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(B_292,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_292) ) ),
    inference(resolution,[status(thm)],[c_947,c_78])).

tff(c_1053,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_1041])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1082,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1053,c_2])).

tff(c_1418,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1082])).

tff(c_1868,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,'#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_1418])).

tff(c_1881,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34,c_1868])).

tff(c_1882,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1866])).

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

tff(c_715,plain,(
    ! [C_200,A_202,E_198,D_199,B_201] : k4_enumset1(A_202,A_202,B_201,C_200,D_199,E_198) = k3_enumset1(A_202,B_201,C_200,D_199,E_198) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ! [F_41,D_39,A_36,C_38,B_37,H_45] : r2_hidden(H_45,k4_enumset1(A_36,B_37,C_38,D_39,H_45,F_41)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_742,plain,(
    ! [A_207,D_205,C_206,B_203,E_204] : r2_hidden(D_205,k3_enumset1(A_207,B_203,C_206,D_205,E_204)) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_40])).

tff(c_746,plain,(
    ! [C_208,A_209,B_210,D_211] : r2_hidden(C_208,k2_enumset1(A_209,B_210,C_208,D_211)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_742])).

tff(c_750,plain,(
    ! [B_212,A_213,C_214] : r2_hidden(B_212,k1_enumset1(A_213,B_212,C_214)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_746])).

tff(c_766,plain,(
    ! [A_219,B_220] : r2_hidden(A_219,k2_tarski(A_219,B_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_750])).

tff(c_769,plain,(
    ! [A_4] : r2_hidden(A_4,k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_766])).

tff(c_1907,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1882,c_769])).

tff(c_100,plain,(
    ! [B_66,A_65] :
      ( k1_tarski(k1_funct_1(B_66,A_65)) = k11_relat_1(B_66,A_65)
      | ~ r2_hidden(A_65,k1_relat_1(B_66))
      | ~ v1_funct_1(B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1929,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1907,c_100])).

tff(c_1932,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_118,c_591,c_1929])).

tff(c_754,plain,(
    ! [A_215,B_216,C_217,D_218] :
      ( k7_relset_1(A_215,B_216,C_217,D_218) = k9_relat_1(C_217,D_218)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_764,plain,(
    ! [D_218] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_218) = k9_relat_1('#skF_6',D_218) ),
    inference(resolution,[status(thm)],[c_114,c_754])).

tff(c_110,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_805,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_764,c_110])).

tff(c_1961,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1932,c_805])).

tff(c_1986,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_1961])).

tff(c_1990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_1986])).

tff(c_1991,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1082])).

tff(c_80,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(A_46,k1_zfmisc_1(B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_292,plain,(
    ! [A_46,A_137,B_138] :
      ( v4_relat_1(A_46,A_137)
      | ~ r1_tarski(A_46,k2_zfmisc_1(A_137,B_138)) ) ),
    inference(resolution,[status(thm)],[c_80,c_277])).

tff(c_2117,plain,(
    ! [A_440] :
      ( v4_relat_1(A_440,k1_relat_1('#skF_6'))
      | ~ r1_tarski(A_440,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1991,c_292])).

tff(c_293,plain,(
    ! [B_139,A_140] :
      ( r1_tarski(k1_relat_1(B_139),A_140)
      | ~ v4_relat_1(B_139,A_140)
      | ~ v1_relat_1(B_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_243,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(A_46)
      | ~ v1_relat_1(B_47)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_80,c_233])).

tff(c_307,plain,(
    ! [B_139,A_140] :
      ( v1_relat_1(k1_relat_1(B_139))
      | ~ v1_relat_1(A_140)
      | ~ v4_relat_1(B_139,A_140)
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_293,c_243])).

tff(c_2129,plain,(
    ! [A_440] :
      ( v1_relat_1(k1_relat_1(A_440))
      | ~ v1_relat_1(k1_relat_1('#skF_6'))
      | ~ v1_relat_1(A_440)
      | ~ r1_tarski(A_440,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2117,c_307])).

tff(c_2282,plain,(
    ~ v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2129])).

tff(c_3181,plain,(
    ! [B_546,B_547] :
      ( k1_tarski(B_546) = k1_relat_1(B_547)
      | k1_relat_1(B_547) = k1_xboole_0
      | ~ v4_relat_1(B_547,k1_tarski(B_546))
      | ~ v1_relat_1(B_547) ) ),
    inference(resolution,[status(thm)],[c_88,c_624])).

tff(c_3208,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_291,c_3181])).

tff(c_3221,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_3208])).

tff(c_3223,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3221])).

tff(c_108,plain,(
    ! [D_77,B_75,C_76,A_74] :
      ( m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(B_75,C_76)))
      | ~ r1_tarski(k1_relat_1(D_77),B_75)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_74,C_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2398,plain,(
    ! [D_491,B_492] :
      ( m1_subset_1(D_491,k1_zfmisc_1(k2_zfmisc_1(B_492,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(D_491),B_492)
      | ~ m1_subset_1(D_491,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1991,c_108])).

tff(c_3077,plain,(
    ! [D_543,B_544] :
      ( r1_tarski(D_543,k2_zfmisc_1(B_544,'#skF_4'))
      | ~ r1_tarski(k1_relat_1(D_543),B_544)
      | ~ m1_subset_1(D_543,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2398,c_78])).

tff(c_3102,plain,(
    ! [D_545] :
      ( r1_tarski(D_545,k2_zfmisc_1(k1_relat_1(D_545),'#skF_4'))
      | ~ m1_subset_1(D_545,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6,c_3077])).

tff(c_104,plain,(
    ! [C_69,A_67,B_68] :
      ( v4_relat_1(C_69,A_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_972,plain,(
    ! [B_283] :
      ( v4_relat_1('#skF_6',B_283)
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_283) ) ),
    inference(resolution,[status(thm)],[c_947,c_104])).

tff(c_3156,plain,
    ( v4_relat_1('#skF_6',k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')),'#skF_4'))
    | ~ m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3102,c_972])).

tff(c_3170,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3156])).

tff(c_3174,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_3170])).

tff(c_3224,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3223,c_3174])).

tff(c_3247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3224])).

tff(c_3248,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_3221])).

tff(c_186,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_114,c_78])).

tff(c_193,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,
    ( k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_186,c_193])).

tff(c_273,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_3255,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3248,c_273])).

tff(c_3265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1991,c_3255])).

tff(c_3267,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3156])).

tff(c_82,plain,(
    ! [B_50,A_48] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2411,plain,(
    ! [D_491,B_492] :
      ( v1_relat_1(D_491)
      | ~ v1_relat_1(k2_zfmisc_1(B_492,'#skF_4'))
      | ~ r1_tarski(k1_relat_1(D_491),B_492)
      | ~ m1_subset_1(D_491,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2398,c_82])).

tff(c_2430,plain,(
    ! [D_493,B_494] :
      ( v1_relat_1(D_493)
      | ~ r1_tarski(k1_relat_1(D_493),B_494)
      | ~ m1_subset_1(D_493,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_2411])).

tff(c_2443,plain,(
    ! [D_493] :
      ( v1_relat_1(D_493)
      | ~ m1_subset_1(D_493,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6,c_2430])).

tff(c_3270,plain,(
    v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3267,c_2443])).

tff(c_3288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2282,c_3270])).

tff(c_3290,plain,(
    v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2129])).

tff(c_32,plain,(
    ! [A_34] : k2_zfmisc_1(A_34,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_329,plain,(
    ! [C_145,A_146] :
      ( v4_relat_1(C_145,A_146)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_277])).

tff(c_333,plain,(
    ! [A_46,A_146] :
      ( v4_relat_1(A_46,A_146)
      | ~ r1_tarski(A_46,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_80,c_329])).

tff(c_1063,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_333,c_1059])).

tff(c_146,plain,(
    ! [A_82,B_83] : v1_relat_1(k2_zfmisc_1(A_82,B_83)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_148,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_146])).

tff(c_335,plain,(
    ! [A_149,A_150,B_151] :
      ( v4_relat_1(A_149,A_150)
      | ~ r1_tarski(A_149,k2_zfmisc_1(A_150,B_151)) ) ),
    inference(resolution,[status(thm)],[c_80,c_277])).

tff(c_360,plain,(
    ! [A_150,B_151] : v4_relat_1(k2_zfmisc_1(A_150,B_151),A_150) ),
    inference(resolution,[status(thm)],[c_6,c_335])).

tff(c_208,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_193])).

tff(c_464,plain,(
    ! [B_159] :
      ( k1_relat_1(B_159) = k1_xboole_0
      | ~ v4_relat_1(B_159,k1_xboole_0)
      | ~ v1_relat_1(B_159) ) ),
    inference(resolution,[status(thm)],[c_293,c_208])).

tff(c_468,plain,(
    ! [B_151] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_151)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_151)) ) ),
    inference(resolution,[status(thm)],[c_360,c_464])).

tff(c_479,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_34,c_34,c_468])).

tff(c_4928,plain,(
    ! [B_669,B_670] :
      ( k1_tarski(B_669) = k1_relat_1(B_670)
      | k1_relat_1(B_670) = k1_xboole_0
      | ~ v4_relat_1(B_670,k1_tarski(B_669))
      | ~ v1_relat_1(B_670) ) ),
    inference(resolution,[status(thm)],[c_88,c_624])).

tff(c_4955,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_291,c_4928])).

tff(c_4968,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_4955])).

tff(c_4969,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4968])).

tff(c_4195,plain,(
    ! [B_635,B_636] :
      ( k1_tarski(B_635) = k1_relat_1(B_636)
      | k1_relat_1(B_636) = k1_xboole_0
      | ~ v4_relat_1(B_636,k1_tarski(B_635))
      | ~ v1_relat_1(B_636) ) ),
    inference(resolution,[status(thm)],[c_88,c_624])).

tff(c_4222,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_291,c_4195])).

tff(c_4235,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_4222])).

tff(c_4236,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4235])).

tff(c_3510,plain,(
    ! [D_593,B_594] :
      ( m1_subset_1(D_593,k1_zfmisc_1(k2_zfmisc_1(B_594,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(D_593),B_594)
      | ~ m1_subset_1(D_593,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1991,c_108])).

tff(c_3832,plain,(
    ! [D_623,B_624] :
      ( r1_tarski(D_623,k2_zfmisc_1(B_624,'#skF_4'))
      | ~ r1_tarski(k1_relat_1(D_623),B_624)
      | ~ m1_subset_1(D_623,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_3510,c_78])).

tff(c_3852,plain,(
    ! [D_625] :
      ( r1_tarski(D_625,k2_zfmisc_1(k1_relat_1(D_625),'#skF_4'))
      | ~ m1_subset_1(D_625,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6,c_3832])).

tff(c_3900,plain,
    ( v4_relat_1('#skF_6',k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')),'#skF_4'))
    | ~ m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3852,c_972])).

tff(c_4038,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3900])).

tff(c_4042,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_4038])).

tff(c_4237,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4236,c_4042])).

tff(c_4261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4237])).

tff(c_4262,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_4235])).

tff(c_1141,plain,(
    ! [B_301,A_302] :
      ( v1_relat_1(k1_relat_1(B_301))
      | ~ v1_relat_1(A_302)
      | ~ v4_relat_1(B_301,A_302)
      | ~ v1_relat_1(B_301) ) ),
    inference(resolution,[status(thm)],[c_293,c_243])).

tff(c_1151,plain,
    ( v1_relat_1(k1_relat_1('#skF_6'))
    | ~ v1_relat_1(k1_tarski('#skF_3'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_291,c_1141])).

tff(c_1166,plain,
    ( v1_relat_1(k1_relat_1('#skF_6'))
    | ~ v1_relat_1(k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_1151])).

tff(c_1168,plain,(
    ~ v1_relat_1(k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1166])).

tff(c_4264,plain,(
    ~ v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4262,c_1168])).

tff(c_4275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3290,c_4264])).

tff(c_4277,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3900])).

tff(c_976,plain,(
    ! [B_283] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(B_283,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_283) ) ),
    inference(resolution,[status(thm)],[c_947,c_78])).

tff(c_3899,plain,
    ( r1_tarski('#skF_6',k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')),'#skF_4'),'#skF_4'))
    | ~ m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3852,c_976])).

tff(c_4604,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')),'#skF_4'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4277,c_3899])).

tff(c_4974,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),'#skF_4'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4969,c_4604])).

tff(c_5011,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_479,c_4974])).

tff(c_5013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1063,c_5011])).

tff(c_5014,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_4968])).

tff(c_5016,plain,(
    ~ v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5014,c_1168])).

tff(c_5027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3290,c_5016])).

tff(c_5028,plain,(
    v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1166])).

tff(c_5635,plain,(
    ! [B_770,B_771] :
      ( k1_tarski(B_770) = k1_relat_1(B_771)
      | k1_relat_1(B_771) = k1_xboole_0
      | ~ v4_relat_1(B_771,k1_tarski(B_770))
      | ~ v1_relat_1(B_771) ) ),
    inference(resolution,[status(thm)],[c_88,c_624])).

tff(c_5662,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_291,c_5635])).

tff(c_5675,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_5662])).

tff(c_5676,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5675])).

tff(c_5308,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1082])).

tff(c_5677,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,'#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5676,c_5308])).

tff(c_5691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34,c_5677])).

tff(c_5692,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_5675])).

tff(c_5729,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5692,c_769])).

tff(c_5744,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_5729,c_100])).

tff(c_5747,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_118,c_591,c_5744])).

tff(c_5748,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5747,c_805])).

tff(c_5773,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_5748])).

tff(c_5777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_5773])).

tff(c_5778,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1082])).

tff(c_361,plain,(
    ! [A_150] : v4_relat_1(k1_xboole_0,A_150) ),
    inference(resolution,[status(thm)],[c_8,c_335])).

tff(c_7770,plain,(
    ! [B_921,B_922] :
      ( k1_tarski(B_921) = k1_relat_1(B_922)
      | k1_relat_1(B_922) = k1_xboole_0
      | ~ v4_relat_1(B_922,k1_tarski(B_921))
      | ~ v1_relat_1(B_922) ) ),
    inference(resolution,[status(thm)],[c_88,c_624])).

tff(c_7797,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_291,c_7770])).

tff(c_7810,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_7797])).

tff(c_7811,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7810])).

tff(c_7019,plain,(
    ! [B_887,B_888] :
      ( k1_tarski(B_887) = k1_relat_1(B_888)
      | k1_relat_1(B_888) = k1_xboole_0
      | ~ v4_relat_1(B_888,k1_tarski(B_887))
      | ~ v1_relat_1(B_888) ) ),
    inference(resolution,[status(thm)],[c_88,c_624])).

tff(c_7046,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_291,c_7019])).

tff(c_7059,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_7046])).

tff(c_7060,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7059])).

tff(c_6310,plain,(
    ! [D_845,B_846] :
      ( m1_subset_1(D_845,k1_zfmisc_1(k2_zfmisc_1(B_846,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(D_845),B_846)
      | ~ m1_subset_1(D_845,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5778,c_108])).

tff(c_6630,plain,(
    ! [D_875,B_876] :
      ( r1_tarski(D_875,k2_zfmisc_1(B_876,'#skF_4'))
      | ~ r1_tarski(k1_relat_1(D_875),B_876)
      | ~ m1_subset_1(D_875,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6310,c_78])).

tff(c_6650,plain,(
    ! [D_877] :
      ( r1_tarski(D_877,k2_zfmisc_1(k1_relat_1(D_877),'#skF_4'))
      | ~ m1_subset_1(D_877,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6,c_6630])).

tff(c_6698,plain,
    ( v4_relat_1('#skF_6',k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')),'#skF_4'))
    | ~ m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6650,c_972])).

tff(c_6849,plain,(
    ~ m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_6698])).

tff(c_6853,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_6849])).

tff(c_7061,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7060,c_6853])).

tff(c_7085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_7061])).

tff(c_7086,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_7059])).

tff(c_7093,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7086,c_273])).

tff(c_7104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5778,c_7093])).

tff(c_7106,plain,(
    m1_subset_1(k1_relat_1('#skF_6'),k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_6698])).

tff(c_5924,plain,(
    ! [C_792] :
      ( v4_relat_1(C_792,k1_relat_1('#skF_6'))
      | ~ m1_subset_1(C_792,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5778,c_104])).

tff(c_5929,plain,(
    ! [C_792] :
      ( v1_relat_1(k1_relat_1(C_792))
      | ~ v1_relat_1(k1_relat_1('#skF_6'))
      | ~ v1_relat_1(C_792)
      | ~ m1_subset_1(C_792,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_5924,c_307])).

tff(c_5938,plain,(
    ! [C_792] :
      ( v1_relat_1(k1_relat_1(C_792))
      | ~ v1_relat_1(C_792)
      | ~ m1_subset_1(C_792,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5028,c_5929])).

tff(c_7117,plain,
    ( v1_relat_1(k1_relat_1(k1_relat_1('#skF_6')))
    | ~ v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_7106,c_5938])).

tff(c_7135,plain,(
    v1_relat_1(k1_relat_1(k1_relat_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5028,c_7117])).

tff(c_540,plain,(
    ! [A_165] :
      ( k1_relat_1(A_165) = k1_xboole_0
      | ~ v1_relat_1(A_165)
      | ~ r1_tarski(A_165,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_333,c_464])).

tff(c_553,plain,(
    ! [B_55] :
      ( k1_relat_1(k1_relat_1(B_55)) = k1_xboole_0
      | ~ v1_relat_1(k1_relat_1(B_55))
      | ~ v4_relat_1(B_55,k1_xboole_0)
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_88,c_540])).

tff(c_7222,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1('#skF_6'))) = k1_xboole_0
    | ~ v4_relat_1(k1_relat_1('#skF_6'),k1_xboole_0)
    | ~ v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_7135,c_553])).

tff(c_7231,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1('#skF_6'))) = k1_xboole_0
    | ~ v4_relat_1(k1_relat_1('#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5028,c_7222])).

tff(c_7439,plain,(
    ~ v4_relat_1(k1_relat_1('#skF_6'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7231])).

tff(c_7815,plain,(
    ~ v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7811,c_7439])).

tff(c_7854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_7815])).

tff(c_7855,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_7810])).

tff(c_7862,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7855,c_273])).

tff(c_7873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5778,c_7862])).

tff(c_7875,plain,(
    v4_relat_1(k1_relat_1('#skF_6'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7231])).

tff(c_308,plain,(
    ! [B_139] :
      ( k1_relat_1(B_139) = k1_xboole_0
      | ~ v4_relat_1(B_139,k1_xboole_0)
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_293,c_208])).

tff(c_7880,plain,
    ( k1_relat_1(k1_relat_1('#skF_6')) = k1_xboole_0
    | ~ v1_relat_1(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_7875,c_308])).

tff(c_7889,plain,(
    k1_relat_1(k1_relat_1('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5028,c_7880])).

tff(c_7105,plain,(
    v4_relat_1('#skF_6',k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')),'#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6698])).

tff(c_7897,plain,(
    v4_relat_1('#skF_6',k2_zfmisc_1(k1_xboole_0,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7889,c_7105])).

tff(c_7902,plain,(
    v4_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7897])).

tff(c_7904,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1059,c_7902])).

tff(c_7905,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_7956,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7905,c_78])).

tff(c_8011,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7956,c_208])).

tff(c_8037,plain,(
    ! [A_3] : r1_tarski('#skF_6',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8011,c_8])).

tff(c_96,plain,(
    ! [A_62] : k9_relat_1(k1_xboole_0,A_62) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8033,plain,(
    ! [A_62] : k9_relat_1('#skF_6',A_62) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8011,c_8011,c_96])).

tff(c_8200,plain,(
    ~ r1_tarski('#skF_6',k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8033,c_805])).

tff(c_8204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8037,c_8200])).

tff(c_8205,plain,(
    k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_8246,plain,(
    ! [C_952,A_953,B_954] :
      ( v4_relat_1(C_952,A_953)
      | ~ m1_subset_1(C_952,k1_zfmisc_1(k2_zfmisc_1(A_953,B_954))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_8268,plain,(
    ! [A_965,A_966,B_967] :
      ( v4_relat_1(A_965,A_966)
      | ~ r1_tarski(A_965,k2_zfmisc_1(A_966,B_967)) ) ),
    inference(resolution,[status(thm)],[c_80,c_8246])).

tff(c_8290,plain,(
    ! [A_970,B_971] : v4_relat_1(k2_zfmisc_1(A_970,B_971),A_970) ),
    inference(resolution,[status(thm)],[c_6,c_8268])).

tff(c_8293,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8205,c_8290])).

tff(c_8492,plain,(
    ! [B_1011,A_1012] :
      ( k7_relat_1(B_1011,A_1012) = B_1011
      | ~ v4_relat_1(B_1011,A_1012)
      | ~ v1_relat_1(B_1011) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_8498,plain,
    ( k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8293,c_8492])).

tff(c_8517,plain,(
    k7_relat_1('#skF_6',k1_tarski('#skF_3')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_8498])).

tff(c_8612,plain,
    ( k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8517,c_94])).

tff(c_8622,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_8612])).

tff(c_84,plain,(
    ! [A_51,B_53] :
      ( k9_relat_1(A_51,k1_tarski(B_53)) = k11_relat_1(A_51,B_53)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8630,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8622,c_84])).

tff(c_8640,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_8630])).

tff(c_112,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_30,plain,(
    ! [B_35,A_34] :
      ( k1_xboole_0 = B_35
      | k1_xboole_0 = A_34
      | k2_zfmisc_1(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8213,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_8205,c_30])).

tff(c_8218,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | k1_xboole_0 != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_8213])).

tff(c_8232,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8218])).

tff(c_8208,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8205,c_114])).

tff(c_8325,plain,(
    ! [B_975,A_976] :
      ( k1_tarski(B_975) = A_976
      | k1_xboole_0 = A_976
      | ~ r1_tarski(A_976,k1_tarski(B_975)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10049,plain,(
    ! [B_1216,B_1217] :
      ( k1_tarski(B_1216) = k1_relat_1(B_1217)
      | k1_relat_1(B_1217) = k1_xboole_0
      | ~ v4_relat_1(B_1217,k1_tarski(B_1216))
      | ~ v1_relat_1(B_1217) ) ),
    inference(resolution,[status(thm)],[c_88,c_8325])).

tff(c_10073,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8293,c_10049])).

tff(c_10097,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_10073])).

tff(c_10106,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_10097])).

tff(c_9335,plain,(
    ! [D_1151,B_1152,C_1153,A_1154] :
      ( m1_subset_1(D_1151,k1_zfmisc_1(k2_zfmisc_1(B_1152,C_1153)))
      | ~ r1_tarski(k1_relat_1(D_1151),B_1152)
      | ~ m1_subset_1(D_1151,k1_zfmisc_1(k2_zfmisc_1(A_1154,C_1153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_9368,plain,(
    ! [D_1161,B_1162] :
      ( m1_subset_1(D_1161,k1_zfmisc_1(k2_zfmisc_1(B_1162,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(D_1161),B_1162)
      | ~ m1_subset_1(D_1161,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8205,c_9335])).

tff(c_9858,plain,(
    ! [D_1212,B_1213] :
      ( r1_tarski(D_1212,k2_zfmisc_1(B_1213,'#skF_4'))
      | ~ r1_tarski(k1_relat_1(D_1212),B_1213)
      | ~ m1_subset_1(D_1212,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_9368,c_78])).

tff(c_9877,plain,(
    ! [D_1212] :
      ( r1_tarski(D_1212,k2_zfmisc_1(k1_relat_1(D_1212),'#skF_4'))
      | ~ m1_subset_1(D_1212,k1_zfmisc_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6,c_9858])).

tff(c_10114,plain,
    ( r1_tarski('#skF_6',k2_zfmisc_1(k1_xboole_0,'#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10106,c_9877])).

tff(c_10186,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8208,c_34,c_10114])).

tff(c_10308,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10186,c_208])).

tff(c_10325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8232,c_10308])).

tff(c_10326,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_10097])).

tff(c_8971,plain,(
    ! [B_1054,D_1052,C_1053,E_1051,A_1055] : k4_enumset1(A_1055,A_1055,B_1054,C_1053,D_1052,E_1051) = k3_enumset1(A_1055,B_1054,C_1053,D_1052,E_1051) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    ! [F_41,D_39,E_40,C_38,B_37,H_45] : r2_hidden(H_45,k4_enumset1(H_45,B_37,C_38,D_39,E_40,F_41)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8998,plain,(
    ! [A_1060,C_1057,D_1058,B_1056,E_1059] : r2_hidden(A_1060,k3_enumset1(A_1060,B_1056,C_1057,D_1058,E_1059)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8971,c_48])).

tff(c_9002,plain,(
    ! [A_1061,B_1062,C_1063,D_1064] : r2_hidden(A_1061,k2_enumset1(A_1061,B_1062,C_1063,D_1064)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8998])).

tff(c_9006,plain,(
    ! [A_1065,B_1066,C_1067] : r2_hidden(A_1065,k1_enumset1(A_1065,B_1066,C_1067)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_9002])).

tff(c_9016,plain,(
    ! [A_1069,B_1070] : r2_hidden(A_1069,k2_tarski(A_1069,B_1070)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_9006])).

tff(c_9019,plain,(
    ! [A_4] : r2_hidden(A_4,k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_9016])).

tff(c_10353,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10326,c_9019])).

tff(c_10397,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10353,c_100])).

tff(c_10400,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_118,c_8640,c_10397])).

tff(c_9033,plain,(
    ! [A_1084,B_1085,C_1086,D_1087] :
      ( k7_relset_1(A_1084,B_1085,C_1086,D_1087) = k9_relat_1(C_1086,D_1087)
      | ~ m1_subset_1(C_1086,k1_zfmisc_1(k2_zfmisc_1(A_1084,B_1085))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_9057,plain,(
    ! [C_1099,D_1100] :
      ( k7_relset_1(k1_tarski('#skF_3'),'#skF_4',C_1099,D_1100) = k9_relat_1(C_1099,D_1100)
      | ~ m1_subset_1(C_1099,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8205,c_9033])).

tff(c_9063,plain,(
    ! [D_1100] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_1100) = k9_relat_1('#skF_6',D_1100) ),
    inference(resolution,[status(thm)],[c_8208,c_9057])).

tff(c_9121,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9063,c_110])).

tff(c_10528,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10400,c_9121])).

tff(c_10553,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_92,c_10528])).

tff(c_10557,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_10553])).

tff(c_10559,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8218])).

tff(c_10566,plain,(
    ! [A_3] : r1_tarski('#skF_6',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10559,c_8])).

tff(c_10562,plain,(
    ! [A_62] : k9_relat_1('#skF_6',A_62) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10559,c_10559,c_96])).

tff(c_10565,plain,(
    ! [B_35] : k2_zfmisc_1('#skF_6',B_35) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10559,c_10559,c_34])).

tff(c_11344,plain,(
    ! [A_1375,B_1376,C_1377,D_1378] :
      ( k7_relset_1(A_1375,B_1376,C_1377,D_1378) = k9_relat_1(C_1377,D_1378)
      | ~ m1_subset_1(C_1377,k1_zfmisc_1(k2_zfmisc_1(A_1375,B_1376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_11870,plain,(
    ! [B_1477,C_1478,D_1479] :
      ( k7_relset_1('#skF_6',B_1477,C_1478,D_1479) = k9_relat_1(C_1478,D_1479)
      | ~ m1_subset_1(C_1478,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10565,c_11344])).

tff(c_11872,plain,(
    ! [B_1477,D_1479] : k7_relset_1('#skF_6',B_1477,'#skF_6',D_1479) = k9_relat_1('#skF_6',D_1479) ),
    inference(resolution,[status(thm)],[c_8208,c_11870])).

tff(c_11877,plain,(
    ! [B_1477,D_1479] : k7_relset_1('#skF_6',B_1477,'#skF_6',D_1479) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10562,c_11872])).

tff(c_10558,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8218])).

tff(c_10585,plain,(
    k1_tarski('#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10559,c_10558])).

tff(c_11255,plain,(
    ! [D_1347,A_1350,B_1349,C_1348,E_1346] : k4_enumset1(A_1350,A_1350,B_1349,C_1348,D_1347,E_1346) = k3_enumset1(A_1350,B_1349,C_1348,D_1347,E_1346) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_11296,plain,(
    ! [A_1354,E_1355,B_1356,C_1357,D_1353] : r2_hidden(D_1353,k3_enumset1(A_1354,B_1356,C_1357,D_1353,E_1355)) ),
    inference(superposition,[status(thm),theory(equality)],[c_11255,c_40])).

tff(c_11300,plain,(
    ! [C_1358,A_1359,B_1360,D_1361] : r2_hidden(C_1358,k2_enumset1(A_1359,B_1360,C_1358,D_1361)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_11296])).

tff(c_11328,plain,(
    ! [B_1364,A_1365,C_1366] : r2_hidden(B_1364,k1_enumset1(A_1365,B_1364,C_1366)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_11300])).

tff(c_11332,plain,(
    ! [A_1367,B_1368] : r2_hidden(A_1367,k2_tarski(A_1367,B_1368)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_11328])).

tff(c_11336,plain,(
    ! [A_1369] : r2_hidden(A_1369,k1_tarski(A_1369)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_11332])).

tff(c_11339,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10585,c_11336])).

tff(c_10622,plain,(
    ! [A_1246] : k9_relat_1('#skF_6',A_1246) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10559,c_10559,c_96])).

tff(c_10628,plain,(
    ! [B_53] :
      ( k11_relat_1('#skF_6',B_53) = '#skF_6'
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10622,c_84])).

tff(c_10640,plain,(
    ! [B_53] : k11_relat_1('#skF_6',B_53) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_10628])).

tff(c_10711,plain,(
    ! [C_1271,A_1272,B_1273] :
      ( v4_relat_1(C_1271,A_1272)
      | ~ m1_subset_1(C_1271,k1_zfmisc_1(k2_zfmisc_1(A_1272,B_1273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_10776,plain,(
    ! [A_1286,A_1287,B_1288] :
      ( v4_relat_1(A_1286,A_1287)
      | ~ r1_tarski(A_1286,k2_zfmisc_1(A_1287,B_1288)) ) ),
    inference(resolution,[status(thm)],[c_80,c_10711])).

tff(c_10793,plain,(
    ! [A_1287,B_1288] : v4_relat_1(k2_zfmisc_1(A_1287,B_1288),A_1287) ),
    inference(resolution,[status(thm)],[c_6,c_10776])).

tff(c_10906,plain,(
    ! [B_1310,A_1311] :
      ( r1_tarski(k1_relat_1(B_1310),A_1311)
      | ~ v4_relat_1(B_1310,A_1311)
      | ~ v1_relat_1(B_1310) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10561,plain,(
    ! [A_3] :
      ( A_3 = '#skF_6'
      | ~ r1_tarski(A_3,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10559,c_10559,c_208])).

tff(c_10938,plain,(
    ! [B_1312] :
      ( k1_relat_1(B_1312) = '#skF_6'
      | ~ v4_relat_1(B_1312,'#skF_6')
      | ~ v1_relat_1(B_1312) ) ),
    inference(resolution,[status(thm)],[c_10906,c_10561])).

tff(c_10942,plain,(
    ! [B_1288] :
      ( k1_relat_1(k2_zfmisc_1('#skF_6',B_1288)) = '#skF_6'
      | ~ v1_relat_1(k2_zfmisc_1('#skF_6',B_1288)) ) ),
    inference(resolution,[status(thm)],[c_10793,c_10938])).

tff(c_10953,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_10565,c_10942])).

tff(c_11395,plain,(
    ! [B_1411,A_1412] :
      ( k1_tarski(k1_funct_1(B_1411,A_1412)) = k11_relat_1(B_1411,A_1412)
      | ~ r2_hidden(A_1412,k1_relat_1(B_1411))
      | ~ v1_funct_1(B_1411)
      | ~ v1_relat_1(B_1411) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_11398,plain,(
    ! [A_1412] :
      ( k1_tarski(k1_funct_1('#skF_6',A_1412)) = k11_relat_1('#skF_6',A_1412)
      | ~ r2_hidden(A_1412,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10953,c_11395])).

tff(c_11407,plain,(
    ! [A_1418] :
      ( k1_tarski(k1_funct_1('#skF_6',A_1418)) = '#skF_6'
      | ~ r2_hidden(A_1418,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_118,c_10640,c_11398])).

tff(c_10587,plain,(
    ~ r1_tarski(k7_relset_1('#skF_6','#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10585,c_110])).

tff(c_11419,plain,
    ( ~ r1_tarski(k7_relset_1('#skF_6','#skF_4','#skF_6','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_3','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_11407,c_10587])).

tff(c_11428,plain,(
    ~ r1_tarski(k7_relset_1('#skF_6','#skF_4','#skF_6','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11339,c_11419])).

tff(c_11879,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11877,c_11428])).

tff(c_11883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10566,c_11879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.32/3.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.60/3.11  
% 8.60/3.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.60/3.11  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 8.60/3.11  
% 8.60/3.11  %Foreground sorts:
% 8.60/3.11  
% 8.60/3.11  
% 8.60/3.11  %Background operators:
% 8.60/3.11  
% 8.60/3.11  
% 8.60/3.11  %Foreground operators:
% 8.60/3.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.60/3.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.60/3.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.60/3.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.60/3.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.60/3.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.60/3.11  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.60/3.11  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.60/3.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.60/3.11  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.60/3.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.60/3.11  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.60/3.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.60/3.11  tff('#skF_5', type, '#skF_5': $i).
% 8.60/3.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.60/3.11  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 8.60/3.11  tff('#skF_6', type, '#skF_6': $i).
% 8.60/3.11  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.60/3.11  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.60/3.11  tff('#skF_3', type, '#skF_3': $i).
% 8.60/3.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.60/3.11  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.60/3.11  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.60/3.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.60/3.11  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.60/3.11  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.60/3.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.60/3.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.60/3.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.60/3.11  tff('#skF_4', type, '#skF_4': $i).
% 8.60/3.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.60/3.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.60/3.11  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.60/3.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.60/3.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.60/3.11  
% 8.60/3.15  tff(f_107, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.60/3.15  tff(f_159, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 8.60/3.15  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.60/3.15  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 8.60/3.15  tff(f_105, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.60/3.15  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.60/3.15  tff(f_147, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 8.60/3.15  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.60/3.15  tff(f_123, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 8.60/3.15  tff(f_115, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 8.60/3.15  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 8.60/3.15  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.60/3.15  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 8.60/3.15  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.60/3.15  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.60/3.15  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.60/3.15  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.60/3.15  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 8.60/3.15  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 8.60/3.15  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 8.60/3.15  tff(f_83, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 8.60/3.15  tff(f_131, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 8.60/3.15  tff(f_141, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.60/3.15  tff(f_117, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 8.60/3.15  tff(c_90, plain, (![A_56, B_57]: (v1_relat_1(k2_zfmisc_1(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.60/3.15  tff(c_114, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 8.60/3.15  tff(c_233, plain, (![B_99, A_100]: (v1_relat_1(B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(A_100)) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.60/3.15  tff(c_236, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_114, c_233])).
% 8.60/3.15  tff(c_242, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_236])).
% 8.60/3.15  tff(c_92, plain, (![B_59, A_58]: (r1_tarski(k9_relat_1(B_59, A_58), k2_relat_1(B_59)) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.60/3.15  tff(c_118, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 8.60/3.15  tff(c_88, plain, (![B_55, A_54]: (r1_tarski(k1_relat_1(B_55), A_54) | ~v4_relat_1(B_55, A_54) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.60/3.15  tff(c_34, plain, (![B_35]: (k2_zfmisc_1(k1_xboole_0, B_35)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.60/3.15  tff(c_897, plain, (![D_275, B_276, C_277, A_278]: (m1_subset_1(D_275, k1_zfmisc_1(k2_zfmisc_1(B_276, C_277))) | ~r1_tarski(k1_relat_1(D_275), B_276) | ~m1_subset_1(D_275, k1_zfmisc_1(k2_zfmisc_1(A_278, C_277))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.60/3.15  tff(c_947, plain, (![B_283]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_283, '#skF_4'))) | ~r1_tarski(k1_relat_1('#skF_6'), B_283))), inference(resolution, [status(thm)], [c_114, c_897])).
% 8.60/3.15  tff(c_967, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_947])).
% 8.60/3.15  tff(c_1040, plain, (~r1_tarski(k1_relat_1('#skF_6'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_967])).
% 8.60/3.15  tff(c_1056, plain, (~v4_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_88, c_1040])).
% 8.60/3.15  tff(c_1059, plain, (~v4_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_242, c_1056])).
% 8.60/3.15  tff(c_277, plain, (![C_136, A_137, B_138]: (v4_relat_1(C_136, A_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.60/3.15  tff(c_291, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_114, c_277])).
% 8.60/3.15  tff(c_372, plain, (![B_155, A_156]: (k7_relat_1(B_155, A_156)=B_155 | ~v4_relat_1(B_155, A_156) | ~v1_relat_1(B_155))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.60/3.15  tff(c_384, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_291, c_372])).
% 8.60/3.15  tff(c_397, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_242, c_384])).
% 8.60/3.15  tff(c_94, plain, (![B_61, A_60]: (k2_relat_1(k7_relat_1(B_61, A_60))=k9_relat_1(B_61, A_60) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.60/3.15  tff(c_423, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_397, c_94])).
% 8.60/3.15  tff(c_427, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_423])).
% 8.60/3.15  tff(c_560, plain, (![A_166, B_167]: (k9_relat_1(A_166, k1_tarski(B_167))=k11_relat_1(A_166, B_167) | ~v1_relat_1(A_166))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.60/3.15  tff(c_579, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_427, c_560])).
% 8.60/3.15  tff(c_591, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_579])).
% 8.60/3.15  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.60/3.15  tff(c_624, plain, (![B_178, A_179]: (k1_tarski(B_178)=A_179 | k1_xboole_0=A_179 | ~r1_tarski(A_179, k1_tarski(B_178)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.60/3.15  tff(c_1826, plain, (![B_419, B_420]: (k1_tarski(B_419)=k1_relat_1(B_420) | k1_relat_1(B_420)=k1_xboole_0 | ~v4_relat_1(B_420, k1_tarski(B_419)) | ~v1_relat_1(B_420))), inference(resolution, [status(thm)], [c_88, c_624])).
% 8.60/3.15  tff(c_1853, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_291, c_1826])).
% 8.60/3.15  tff(c_1866, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_242, c_1853])).
% 8.60/3.15  tff(c_1867, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1866])).
% 8.60/3.15  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.60/3.15  tff(c_78, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.60/3.15  tff(c_1041, plain, (![B_292]: (r1_tarski('#skF_6', k2_zfmisc_1(B_292, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_6'), B_292))), inference(resolution, [status(thm)], [c_947, c_78])).
% 8.60/3.15  tff(c_1053, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1041])).
% 8.60/3.15  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.60/3.15  tff(c_1082, plain, (k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_1053, c_2])).
% 8.60/3.15  tff(c_1418, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1082])).
% 8.60/3.15  tff(c_1868, plain, (~r1_tarski(k2_zfmisc_1(k1_xboole_0, '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_1418])).
% 8.60/3.15  tff(c_1881, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_34, c_1868])).
% 8.60/3.15  tff(c_1882, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_1866])).
% 8.60/3.15  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.60/3.15  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.60/3.15  tff(c_14, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.60/3.15  tff(c_16, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.60/3.15  tff(c_715, plain, (![C_200, A_202, E_198, D_199, B_201]: (k4_enumset1(A_202, A_202, B_201, C_200, D_199, E_198)=k3_enumset1(A_202, B_201, C_200, D_199, E_198))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.60/3.15  tff(c_40, plain, (![F_41, D_39, A_36, C_38, B_37, H_45]: (r2_hidden(H_45, k4_enumset1(A_36, B_37, C_38, D_39, H_45, F_41)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.60/3.15  tff(c_742, plain, (![A_207, D_205, C_206, B_203, E_204]: (r2_hidden(D_205, k3_enumset1(A_207, B_203, C_206, D_205, E_204)))), inference(superposition, [status(thm), theory('equality')], [c_715, c_40])).
% 8.60/3.15  tff(c_746, plain, (![C_208, A_209, B_210, D_211]: (r2_hidden(C_208, k2_enumset1(A_209, B_210, C_208, D_211)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_742])).
% 8.60/3.15  tff(c_750, plain, (![B_212, A_213, C_214]: (r2_hidden(B_212, k1_enumset1(A_213, B_212, C_214)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_746])).
% 8.60/3.15  tff(c_766, plain, (![A_219, B_220]: (r2_hidden(A_219, k2_tarski(A_219, B_220)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_750])).
% 8.60/3.15  tff(c_769, plain, (![A_4]: (r2_hidden(A_4, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_766])).
% 8.60/3.15  tff(c_1907, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1882, c_769])).
% 8.60/3.15  tff(c_100, plain, (![B_66, A_65]: (k1_tarski(k1_funct_1(B_66, A_65))=k11_relat_1(B_66, A_65) | ~r2_hidden(A_65, k1_relat_1(B_66)) | ~v1_funct_1(B_66) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.60/3.15  tff(c_1929, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1907, c_100])).
% 8.60/3.15  tff(c_1932, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_118, c_591, c_1929])).
% 8.60/3.15  tff(c_754, plain, (![A_215, B_216, C_217, D_218]: (k7_relset_1(A_215, B_216, C_217, D_218)=k9_relat_1(C_217, D_218) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.60/3.15  tff(c_764, plain, (![D_218]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_218)=k9_relat_1('#skF_6', D_218))), inference(resolution, [status(thm)], [c_114, c_754])).
% 8.60/3.15  tff(c_110, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_159])).
% 8.60/3.15  tff(c_805, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_764, c_110])).
% 8.60/3.15  tff(c_1961, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1932, c_805])).
% 8.60/3.15  tff(c_1986, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_92, c_1961])).
% 8.60/3.15  tff(c_1990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_1986])).
% 8.60/3.15  tff(c_1991, plain, (k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_1082])).
% 8.60/3.15  tff(c_80, plain, (![A_46, B_47]: (m1_subset_1(A_46, k1_zfmisc_1(B_47)) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.60/3.15  tff(c_292, plain, (![A_46, A_137, B_138]: (v4_relat_1(A_46, A_137) | ~r1_tarski(A_46, k2_zfmisc_1(A_137, B_138)))), inference(resolution, [status(thm)], [c_80, c_277])).
% 8.60/3.15  tff(c_2117, plain, (![A_440]: (v4_relat_1(A_440, k1_relat_1('#skF_6')) | ~r1_tarski(A_440, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1991, c_292])).
% 8.60/3.15  tff(c_293, plain, (![B_139, A_140]: (r1_tarski(k1_relat_1(B_139), A_140) | ~v4_relat_1(B_139, A_140) | ~v1_relat_1(B_139))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.60/3.15  tff(c_243, plain, (![A_46, B_47]: (v1_relat_1(A_46) | ~v1_relat_1(B_47) | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_80, c_233])).
% 8.60/3.15  tff(c_307, plain, (![B_139, A_140]: (v1_relat_1(k1_relat_1(B_139)) | ~v1_relat_1(A_140) | ~v4_relat_1(B_139, A_140) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_293, c_243])).
% 8.60/3.15  tff(c_2129, plain, (![A_440]: (v1_relat_1(k1_relat_1(A_440)) | ~v1_relat_1(k1_relat_1('#skF_6')) | ~v1_relat_1(A_440) | ~r1_tarski(A_440, '#skF_6'))), inference(resolution, [status(thm)], [c_2117, c_307])).
% 8.60/3.15  tff(c_2282, plain, (~v1_relat_1(k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2129])).
% 8.60/3.15  tff(c_3181, plain, (![B_546, B_547]: (k1_tarski(B_546)=k1_relat_1(B_547) | k1_relat_1(B_547)=k1_xboole_0 | ~v4_relat_1(B_547, k1_tarski(B_546)) | ~v1_relat_1(B_547))), inference(resolution, [status(thm)], [c_88, c_624])).
% 8.60/3.15  tff(c_3208, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_291, c_3181])).
% 8.60/3.15  tff(c_3221, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_242, c_3208])).
% 8.60/3.15  tff(c_3223, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3221])).
% 8.60/3.15  tff(c_108, plain, (![D_77, B_75, C_76, A_74]: (m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(B_75, C_76))) | ~r1_tarski(k1_relat_1(D_77), B_75) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_74, C_76))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.60/3.15  tff(c_2398, plain, (![D_491, B_492]: (m1_subset_1(D_491, k1_zfmisc_1(k2_zfmisc_1(B_492, '#skF_4'))) | ~r1_tarski(k1_relat_1(D_491), B_492) | ~m1_subset_1(D_491, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1991, c_108])).
% 8.60/3.15  tff(c_3077, plain, (![D_543, B_544]: (r1_tarski(D_543, k2_zfmisc_1(B_544, '#skF_4')) | ~r1_tarski(k1_relat_1(D_543), B_544) | ~m1_subset_1(D_543, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_2398, c_78])).
% 8.60/3.15  tff(c_3102, plain, (![D_545]: (r1_tarski(D_545, k2_zfmisc_1(k1_relat_1(D_545), '#skF_4')) | ~m1_subset_1(D_545, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_6, c_3077])).
% 8.60/3.15  tff(c_104, plain, (![C_69, A_67, B_68]: (v4_relat_1(C_69, A_67) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.60/3.15  tff(c_972, plain, (![B_283]: (v4_relat_1('#skF_6', B_283) | ~r1_tarski(k1_relat_1('#skF_6'), B_283))), inference(resolution, [status(thm)], [c_947, c_104])).
% 8.60/3.15  tff(c_3156, plain, (v4_relat_1('#skF_6', k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')), '#skF_4')) | ~m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_3102, c_972])).
% 8.60/3.15  tff(c_3170, plain, (~m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_3156])).
% 8.60/3.15  tff(c_3174, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_80, c_3170])).
% 8.60/3.15  tff(c_3224, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3223, c_3174])).
% 8.60/3.15  tff(c_3247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_3224])).
% 8.60/3.15  tff(c_3248, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_3221])).
% 8.60/3.15  tff(c_186, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_114, c_78])).
% 8.60/3.15  tff(c_193, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(B_94, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.60/3.15  tff(c_203, plain, (k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_186, c_193])).
% 8.60/3.15  tff(c_273, plain, (~r1_tarski(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_203])).
% 8.60/3.15  tff(c_3255, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3248, c_273])).
% 8.60/3.15  tff(c_3265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1991, c_3255])).
% 8.60/3.15  tff(c_3267, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_3156])).
% 8.60/3.15  tff(c_82, plain, (![B_50, A_48]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_48)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.60/3.15  tff(c_2411, plain, (![D_491, B_492]: (v1_relat_1(D_491) | ~v1_relat_1(k2_zfmisc_1(B_492, '#skF_4')) | ~r1_tarski(k1_relat_1(D_491), B_492) | ~m1_subset_1(D_491, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_2398, c_82])).
% 8.60/3.15  tff(c_2430, plain, (![D_493, B_494]: (v1_relat_1(D_493) | ~r1_tarski(k1_relat_1(D_493), B_494) | ~m1_subset_1(D_493, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_2411])).
% 8.60/3.15  tff(c_2443, plain, (![D_493]: (v1_relat_1(D_493) | ~m1_subset_1(D_493, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_6, c_2430])).
% 8.60/3.15  tff(c_3270, plain, (v1_relat_1(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_3267, c_2443])).
% 8.60/3.15  tff(c_3288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2282, c_3270])).
% 8.60/3.15  tff(c_3290, plain, (v1_relat_1(k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2129])).
% 8.60/3.15  tff(c_32, plain, (![A_34]: (k2_zfmisc_1(A_34, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.60/3.15  tff(c_329, plain, (![C_145, A_146]: (v4_relat_1(C_145, A_146) | ~m1_subset_1(C_145, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_277])).
% 8.60/3.15  tff(c_333, plain, (![A_46, A_146]: (v4_relat_1(A_46, A_146) | ~r1_tarski(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_80, c_329])).
% 8.60/3.15  tff(c_1063, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_333, c_1059])).
% 8.60/3.15  tff(c_146, plain, (![A_82, B_83]: (v1_relat_1(k2_zfmisc_1(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.60/3.15  tff(c_148, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_146])).
% 8.60/3.15  tff(c_335, plain, (![A_149, A_150, B_151]: (v4_relat_1(A_149, A_150) | ~r1_tarski(A_149, k2_zfmisc_1(A_150, B_151)))), inference(resolution, [status(thm)], [c_80, c_277])).
% 8.60/3.15  tff(c_360, plain, (![A_150, B_151]: (v4_relat_1(k2_zfmisc_1(A_150, B_151), A_150))), inference(resolution, [status(thm)], [c_6, c_335])).
% 8.60/3.15  tff(c_208, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_193])).
% 8.60/3.15  tff(c_464, plain, (![B_159]: (k1_relat_1(B_159)=k1_xboole_0 | ~v4_relat_1(B_159, k1_xboole_0) | ~v1_relat_1(B_159))), inference(resolution, [status(thm)], [c_293, c_208])).
% 8.60/3.15  tff(c_468, plain, (![B_151]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_151))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_151)))), inference(resolution, [status(thm)], [c_360, c_464])).
% 8.60/3.15  tff(c_479, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_148, c_34, c_34, c_468])).
% 8.60/3.15  tff(c_4928, plain, (![B_669, B_670]: (k1_tarski(B_669)=k1_relat_1(B_670) | k1_relat_1(B_670)=k1_xboole_0 | ~v4_relat_1(B_670, k1_tarski(B_669)) | ~v1_relat_1(B_670))), inference(resolution, [status(thm)], [c_88, c_624])).
% 8.60/3.15  tff(c_4955, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_291, c_4928])).
% 8.60/3.15  tff(c_4968, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_242, c_4955])).
% 8.60/3.15  tff(c_4969, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4968])).
% 8.60/3.15  tff(c_4195, plain, (![B_635, B_636]: (k1_tarski(B_635)=k1_relat_1(B_636) | k1_relat_1(B_636)=k1_xboole_0 | ~v4_relat_1(B_636, k1_tarski(B_635)) | ~v1_relat_1(B_636))), inference(resolution, [status(thm)], [c_88, c_624])).
% 8.60/3.15  tff(c_4222, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_291, c_4195])).
% 8.60/3.15  tff(c_4235, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_242, c_4222])).
% 8.60/3.15  tff(c_4236, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4235])).
% 8.60/3.15  tff(c_3510, plain, (![D_593, B_594]: (m1_subset_1(D_593, k1_zfmisc_1(k2_zfmisc_1(B_594, '#skF_4'))) | ~r1_tarski(k1_relat_1(D_593), B_594) | ~m1_subset_1(D_593, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1991, c_108])).
% 8.60/3.15  tff(c_3832, plain, (![D_623, B_624]: (r1_tarski(D_623, k2_zfmisc_1(B_624, '#skF_4')) | ~r1_tarski(k1_relat_1(D_623), B_624) | ~m1_subset_1(D_623, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_3510, c_78])).
% 8.60/3.15  tff(c_3852, plain, (![D_625]: (r1_tarski(D_625, k2_zfmisc_1(k1_relat_1(D_625), '#skF_4')) | ~m1_subset_1(D_625, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_6, c_3832])).
% 8.60/3.15  tff(c_3900, plain, (v4_relat_1('#skF_6', k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')), '#skF_4')) | ~m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_3852, c_972])).
% 8.60/3.15  tff(c_4038, plain, (~m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_3900])).
% 8.60/3.15  tff(c_4042, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_80, c_4038])).
% 8.60/3.15  tff(c_4237, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4236, c_4042])).
% 8.60/3.15  tff(c_4261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_4237])).
% 8.60/3.15  tff(c_4262, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_4235])).
% 8.60/3.15  tff(c_1141, plain, (![B_301, A_302]: (v1_relat_1(k1_relat_1(B_301)) | ~v1_relat_1(A_302) | ~v4_relat_1(B_301, A_302) | ~v1_relat_1(B_301))), inference(resolution, [status(thm)], [c_293, c_243])).
% 8.60/3.15  tff(c_1151, plain, (v1_relat_1(k1_relat_1('#skF_6')) | ~v1_relat_1(k1_tarski('#skF_3')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_291, c_1141])).
% 8.60/3.15  tff(c_1166, plain, (v1_relat_1(k1_relat_1('#skF_6')) | ~v1_relat_1(k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_1151])).
% 8.60/3.15  tff(c_1168, plain, (~v1_relat_1(k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_1166])).
% 8.60/3.15  tff(c_4264, plain, (~v1_relat_1(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4262, c_1168])).
% 8.60/3.15  tff(c_4275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3290, c_4264])).
% 8.60/3.15  tff(c_4277, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_3900])).
% 8.60/3.15  tff(c_976, plain, (![B_283]: (r1_tarski('#skF_6', k2_zfmisc_1(B_283, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_6'), B_283))), inference(resolution, [status(thm)], [c_947, c_78])).
% 8.60/3.15  tff(c_3899, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')), '#skF_4'), '#skF_4')) | ~m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_3852, c_976])).
% 8.60/3.15  tff(c_4604, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')), '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4277, c_3899])).
% 8.60/3.15  tff(c_4974, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0), '#skF_4'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4969, c_4604])).
% 8.60/3.15  tff(c_5011, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_479, c_4974])).
% 8.60/3.15  tff(c_5013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1063, c_5011])).
% 8.60/3.15  tff(c_5014, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_4968])).
% 8.60/3.15  tff(c_5016, plain, (~v1_relat_1(k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5014, c_1168])).
% 8.60/3.15  tff(c_5027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3290, c_5016])).
% 8.60/3.15  tff(c_5028, plain, (v1_relat_1(k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1166])).
% 8.60/3.15  tff(c_5635, plain, (![B_770, B_771]: (k1_tarski(B_770)=k1_relat_1(B_771) | k1_relat_1(B_771)=k1_xboole_0 | ~v4_relat_1(B_771, k1_tarski(B_770)) | ~v1_relat_1(B_771))), inference(resolution, [status(thm)], [c_88, c_624])).
% 8.60/3.15  tff(c_5662, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_291, c_5635])).
% 8.60/3.15  tff(c_5675, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_242, c_5662])).
% 8.60/3.15  tff(c_5676, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5675])).
% 8.60/3.15  tff(c_5308, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1082])).
% 8.60/3.15  tff(c_5677, plain, (~r1_tarski(k2_zfmisc_1(k1_xboole_0, '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5676, c_5308])).
% 8.60/3.15  tff(c_5691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_34, c_5677])).
% 8.60/3.15  tff(c_5692, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_5675])).
% 8.60/3.15  tff(c_5729, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_5692, c_769])).
% 8.60/3.15  tff(c_5744, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_5729, c_100])).
% 8.60/3.15  tff(c_5747, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_118, c_591, c_5744])).
% 8.60/3.15  tff(c_5748, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5747, c_805])).
% 8.60/3.15  tff(c_5773, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_92, c_5748])).
% 8.60/3.15  tff(c_5777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_5773])).
% 8.60/3.15  tff(c_5778, plain, (k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_1082])).
% 8.60/3.15  tff(c_361, plain, (![A_150]: (v4_relat_1(k1_xboole_0, A_150))), inference(resolution, [status(thm)], [c_8, c_335])).
% 8.60/3.15  tff(c_7770, plain, (![B_921, B_922]: (k1_tarski(B_921)=k1_relat_1(B_922) | k1_relat_1(B_922)=k1_xboole_0 | ~v4_relat_1(B_922, k1_tarski(B_921)) | ~v1_relat_1(B_922))), inference(resolution, [status(thm)], [c_88, c_624])).
% 8.60/3.15  tff(c_7797, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_291, c_7770])).
% 8.60/3.15  tff(c_7810, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_242, c_7797])).
% 8.60/3.15  tff(c_7811, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7810])).
% 8.60/3.15  tff(c_7019, plain, (![B_887, B_888]: (k1_tarski(B_887)=k1_relat_1(B_888) | k1_relat_1(B_888)=k1_xboole_0 | ~v4_relat_1(B_888, k1_tarski(B_887)) | ~v1_relat_1(B_888))), inference(resolution, [status(thm)], [c_88, c_624])).
% 8.60/3.15  tff(c_7046, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_291, c_7019])).
% 8.60/3.15  tff(c_7059, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_242, c_7046])).
% 8.60/3.15  tff(c_7060, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7059])).
% 8.60/3.15  tff(c_6310, plain, (![D_845, B_846]: (m1_subset_1(D_845, k1_zfmisc_1(k2_zfmisc_1(B_846, '#skF_4'))) | ~r1_tarski(k1_relat_1(D_845), B_846) | ~m1_subset_1(D_845, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_5778, c_108])).
% 8.60/3.15  tff(c_6630, plain, (![D_875, B_876]: (r1_tarski(D_875, k2_zfmisc_1(B_876, '#skF_4')) | ~r1_tarski(k1_relat_1(D_875), B_876) | ~m1_subset_1(D_875, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_6310, c_78])).
% 8.60/3.15  tff(c_6650, plain, (![D_877]: (r1_tarski(D_877, k2_zfmisc_1(k1_relat_1(D_877), '#skF_4')) | ~m1_subset_1(D_877, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_6, c_6630])).
% 8.60/3.15  tff(c_6698, plain, (v4_relat_1('#skF_6', k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')), '#skF_4')) | ~m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_6650, c_972])).
% 8.60/3.15  tff(c_6849, plain, (~m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_6698])).
% 8.60/3.15  tff(c_6853, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_80, c_6849])).
% 8.60/3.15  tff(c_7061, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7060, c_6853])).
% 8.60/3.15  tff(c_7085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_7061])).
% 8.60/3.15  tff(c_7086, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_7059])).
% 8.60/3.15  tff(c_7093, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7086, c_273])).
% 8.60/3.15  tff(c_7104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5778, c_7093])).
% 8.60/3.15  tff(c_7106, plain, (m1_subset_1(k1_relat_1('#skF_6'), k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_6698])).
% 8.60/3.15  tff(c_5924, plain, (![C_792]: (v4_relat_1(C_792, k1_relat_1('#skF_6')) | ~m1_subset_1(C_792, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_5778, c_104])).
% 8.60/3.15  tff(c_5929, plain, (![C_792]: (v1_relat_1(k1_relat_1(C_792)) | ~v1_relat_1(k1_relat_1('#skF_6')) | ~v1_relat_1(C_792) | ~m1_subset_1(C_792, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_5924, c_307])).
% 8.60/3.15  tff(c_5938, plain, (![C_792]: (v1_relat_1(k1_relat_1(C_792)) | ~v1_relat_1(C_792) | ~m1_subset_1(C_792, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_5028, c_5929])).
% 8.60/3.15  tff(c_7117, plain, (v1_relat_1(k1_relat_1(k1_relat_1('#skF_6'))) | ~v1_relat_1(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7106, c_5938])).
% 8.60/3.15  tff(c_7135, plain, (v1_relat_1(k1_relat_1(k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_5028, c_7117])).
% 8.60/3.15  tff(c_540, plain, (![A_165]: (k1_relat_1(A_165)=k1_xboole_0 | ~v1_relat_1(A_165) | ~r1_tarski(A_165, k1_xboole_0))), inference(resolution, [status(thm)], [c_333, c_464])).
% 8.60/3.15  tff(c_553, plain, (![B_55]: (k1_relat_1(k1_relat_1(B_55))=k1_xboole_0 | ~v1_relat_1(k1_relat_1(B_55)) | ~v4_relat_1(B_55, k1_xboole_0) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_88, c_540])).
% 8.60/3.15  tff(c_7222, plain, (k1_relat_1(k1_relat_1(k1_relat_1('#skF_6')))=k1_xboole_0 | ~v4_relat_1(k1_relat_1('#skF_6'), k1_xboole_0) | ~v1_relat_1(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7135, c_553])).
% 8.60/3.15  tff(c_7231, plain, (k1_relat_1(k1_relat_1(k1_relat_1('#skF_6')))=k1_xboole_0 | ~v4_relat_1(k1_relat_1('#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5028, c_7222])).
% 8.60/3.15  tff(c_7439, plain, (~v4_relat_1(k1_relat_1('#skF_6'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7231])).
% 8.60/3.15  tff(c_7815, plain, (~v4_relat_1(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7811, c_7439])).
% 8.60/3.15  tff(c_7854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_361, c_7815])).
% 8.60/3.15  tff(c_7855, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_7810])).
% 8.60/3.15  tff(c_7862, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7855, c_273])).
% 8.60/3.15  tff(c_7873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5778, c_7862])).
% 8.60/3.15  tff(c_7875, plain, (v4_relat_1(k1_relat_1('#skF_6'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_7231])).
% 8.60/3.15  tff(c_308, plain, (![B_139]: (k1_relat_1(B_139)=k1_xboole_0 | ~v4_relat_1(B_139, k1_xboole_0) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_293, c_208])).
% 8.60/3.15  tff(c_7880, plain, (k1_relat_1(k1_relat_1('#skF_6'))=k1_xboole_0 | ~v1_relat_1(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7875, c_308])).
% 8.60/3.15  tff(c_7889, plain, (k1_relat_1(k1_relat_1('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5028, c_7880])).
% 8.60/3.15  tff(c_7105, plain, (v4_relat_1('#skF_6', k2_zfmisc_1(k1_relat_1(k1_relat_1('#skF_6')), '#skF_4'))), inference(splitRight, [status(thm)], [c_6698])).
% 8.60/3.15  tff(c_7897, plain, (v4_relat_1('#skF_6', k2_zfmisc_1(k1_xboole_0, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7889, c_7105])).
% 8.60/3.15  tff(c_7902, plain, (v4_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7897])).
% 8.60/3.15  tff(c_7904, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1059, c_7902])).
% 8.60/3.15  tff(c_7905, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_967])).
% 8.60/3.15  tff(c_7956, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_7905, c_78])).
% 8.60/3.15  tff(c_8011, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_7956, c_208])).
% 8.60/3.15  tff(c_8037, plain, (![A_3]: (r1_tarski('#skF_6', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8011, c_8])).
% 8.60/3.15  tff(c_96, plain, (![A_62]: (k9_relat_1(k1_xboole_0, A_62)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.60/3.15  tff(c_8033, plain, (![A_62]: (k9_relat_1('#skF_6', A_62)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8011, c_8011, c_96])).
% 8.60/3.15  tff(c_8200, plain, (~r1_tarski('#skF_6', k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8033, c_805])).
% 8.60/3.15  tff(c_8204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8037, c_8200])).
% 8.60/3.15  tff(c_8205, plain, (k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_203])).
% 8.60/3.15  tff(c_8246, plain, (![C_952, A_953, B_954]: (v4_relat_1(C_952, A_953) | ~m1_subset_1(C_952, k1_zfmisc_1(k2_zfmisc_1(A_953, B_954))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.60/3.15  tff(c_8268, plain, (![A_965, A_966, B_967]: (v4_relat_1(A_965, A_966) | ~r1_tarski(A_965, k2_zfmisc_1(A_966, B_967)))), inference(resolution, [status(thm)], [c_80, c_8246])).
% 8.60/3.15  tff(c_8290, plain, (![A_970, B_971]: (v4_relat_1(k2_zfmisc_1(A_970, B_971), A_970))), inference(resolution, [status(thm)], [c_6, c_8268])).
% 8.60/3.15  tff(c_8293, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8205, c_8290])).
% 8.60/3.15  tff(c_8492, plain, (![B_1011, A_1012]: (k7_relat_1(B_1011, A_1012)=B_1011 | ~v4_relat_1(B_1011, A_1012) | ~v1_relat_1(B_1011))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.60/3.15  tff(c_8498, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8293, c_8492])).
% 8.60/3.15  tff(c_8517, plain, (k7_relat_1('#skF_6', k1_tarski('#skF_3'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_242, c_8498])).
% 8.60/3.15  tff(c_8612, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8517, c_94])).
% 8.60/3.15  tff(c_8622, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_8612])).
% 8.60/3.15  tff(c_84, plain, (![A_51, B_53]: (k9_relat_1(A_51, k1_tarski(B_53))=k11_relat_1(A_51, B_53) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.60/3.15  tff(c_8630, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8622, c_84])).
% 8.60/3.15  tff(c_8640, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_8630])).
% 8.60/3.15  tff(c_112, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_159])).
% 8.60/3.15  tff(c_30, plain, (![B_35, A_34]: (k1_xboole_0=B_35 | k1_xboole_0=A_34 | k2_zfmisc_1(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.60/3.15  tff(c_8213, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_8205, c_30])).
% 8.60/3.15  tff(c_8218, plain, (k1_tarski('#skF_3')=k1_xboole_0 | k1_xboole_0!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_112, c_8213])).
% 8.60/3.15  tff(c_8232, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_8218])).
% 8.60/3.15  tff(c_8208, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_8205, c_114])).
% 8.60/3.15  tff(c_8325, plain, (![B_975, A_976]: (k1_tarski(B_975)=A_976 | k1_xboole_0=A_976 | ~r1_tarski(A_976, k1_tarski(B_975)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 8.60/3.15  tff(c_10049, plain, (![B_1216, B_1217]: (k1_tarski(B_1216)=k1_relat_1(B_1217) | k1_relat_1(B_1217)=k1_xboole_0 | ~v4_relat_1(B_1217, k1_tarski(B_1216)) | ~v1_relat_1(B_1217))), inference(resolution, [status(thm)], [c_88, c_8325])).
% 8.60/3.15  tff(c_10073, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8293, c_10049])).
% 8.60/3.15  tff(c_10097, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_242, c_10073])).
% 8.60/3.15  tff(c_10106, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_10097])).
% 8.60/3.15  tff(c_9335, plain, (![D_1151, B_1152, C_1153, A_1154]: (m1_subset_1(D_1151, k1_zfmisc_1(k2_zfmisc_1(B_1152, C_1153))) | ~r1_tarski(k1_relat_1(D_1151), B_1152) | ~m1_subset_1(D_1151, k1_zfmisc_1(k2_zfmisc_1(A_1154, C_1153))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.60/3.15  tff(c_9368, plain, (![D_1161, B_1162]: (m1_subset_1(D_1161, k1_zfmisc_1(k2_zfmisc_1(B_1162, '#skF_4'))) | ~r1_tarski(k1_relat_1(D_1161), B_1162) | ~m1_subset_1(D_1161, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8205, c_9335])).
% 8.60/3.15  tff(c_9858, plain, (![D_1212, B_1213]: (r1_tarski(D_1212, k2_zfmisc_1(B_1213, '#skF_4')) | ~r1_tarski(k1_relat_1(D_1212), B_1213) | ~m1_subset_1(D_1212, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_9368, c_78])).
% 8.60/3.15  tff(c_9877, plain, (![D_1212]: (r1_tarski(D_1212, k2_zfmisc_1(k1_relat_1(D_1212), '#skF_4')) | ~m1_subset_1(D_1212, k1_zfmisc_1('#skF_6')))), inference(resolution, [status(thm)], [c_6, c_9858])).
% 8.60/3.15  tff(c_10114, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_xboole_0, '#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10106, c_9877])).
% 8.60/3.15  tff(c_10186, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8208, c_34, c_10114])).
% 8.60/3.15  tff(c_10308, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_10186, c_208])).
% 8.60/3.15  tff(c_10325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8232, c_10308])).
% 8.60/3.15  tff(c_10326, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_10097])).
% 8.60/3.15  tff(c_8971, plain, (![B_1054, D_1052, C_1053, E_1051, A_1055]: (k4_enumset1(A_1055, A_1055, B_1054, C_1053, D_1052, E_1051)=k3_enumset1(A_1055, B_1054, C_1053, D_1052, E_1051))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.60/3.15  tff(c_48, plain, (![F_41, D_39, E_40, C_38, B_37, H_45]: (r2_hidden(H_45, k4_enumset1(H_45, B_37, C_38, D_39, E_40, F_41)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.60/3.15  tff(c_8998, plain, (![A_1060, C_1057, D_1058, B_1056, E_1059]: (r2_hidden(A_1060, k3_enumset1(A_1060, B_1056, C_1057, D_1058, E_1059)))), inference(superposition, [status(thm), theory('equality')], [c_8971, c_48])).
% 8.60/3.15  tff(c_9002, plain, (![A_1061, B_1062, C_1063, D_1064]: (r2_hidden(A_1061, k2_enumset1(A_1061, B_1062, C_1063, D_1064)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_8998])).
% 8.60/3.15  tff(c_9006, plain, (![A_1065, B_1066, C_1067]: (r2_hidden(A_1065, k1_enumset1(A_1065, B_1066, C_1067)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_9002])).
% 8.60/3.15  tff(c_9016, plain, (![A_1069, B_1070]: (r2_hidden(A_1069, k2_tarski(A_1069, B_1070)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_9006])).
% 8.60/3.15  tff(c_9019, plain, (![A_4]: (r2_hidden(A_4, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_9016])).
% 8.60/3.15  tff(c_10353, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10326, c_9019])).
% 8.60/3.15  tff(c_10397, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10353, c_100])).
% 8.60/3.15  tff(c_10400, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_118, c_8640, c_10397])).
% 8.60/3.15  tff(c_9033, plain, (![A_1084, B_1085, C_1086, D_1087]: (k7_relset_1(A_1084, B_1085, C_1086, D_1087)=k9_relat_1(C_1086, D_1087) | ~m1_subset_1(C_1086, k1_zfmisc_1(k2_zfmisc_1(A_1084, B_1085))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.60/3.15  tff(c_9057, plain, (![C_1099, D_1100]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', C_1099, D_1100)=k9_relat_1(C_1099, D_1100) | ~m1_subset_1(C_1099, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_8205, c_9033])).
% 8.60/3.15  tff(c_9063, plain, (![D_1100]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_1100)=k9_relat_1('#skF_6', D_1100))), inference(resolution, [status(thm)], [c_8208, c_9057])).
% 8.60/3.15  tff(c_9121, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9063, c_110])).
% 8.60/3.15  tff(c_10528, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10400, c_9121])).
% 8.60/3.15  tff(c_10553, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_92, c_10528])).
% 8.60/3.15  tff(c_10557, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_10553])).
% 8.60/3.15  tff(c_10559, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_8218])).
% 8.60/3.15  tff(c_10566, plain, (![A_3]: (r1_tarski('#skF_6', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_10559, c_8])).
% 8.60/3.15  tff(c_10562, plain, (![A_62]: (k9_relat_1('#skF_6', A_62)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10559, c_10559, c_96])).
% 8.60/3.15  tff(c_10565, plain, (![B_35]: (k2_zfmisc_1('#skF_6', B_35)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10559, c_10559, c_34])).
% 8.60/3.15  tff(c_11344, plain, (![A_1375, B_1376, C_1377, D_1378]: (k7_relset_1(A_1375, B_1376, C_1377, D_1378)=k9_relat_1(C_1377, D_1378) | ~m1_subset_1(C_1377, k1_zfmisc_1(k2_zfmisc_1(A_1375, B_1376))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.60/3.15  tff(c_11870, plain, (![B_1477, C_1478, D_1479]: (k7_relset_1('#skF_6', B_1477, C_1478, D_1479)=k9_relat_1(C_1478, D_1479) | ~m1_subset_1(C_1478, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_10565, c_11344])).
% 8.60/3.15  tff(c_11872, plain, (![B_1477, D_1479]: (k7_relset_1('#skF_6', B_1477, '#skF_6', D_1479)=k9_relat_1('#skF_6', D_1479))), inference(resolution, [status(thm)], [c_8208, c_11870])).
% 8.60/3.15  tff(c_11877, plain, (![B_1477, D_1479]: (k7_relset_1('#skF_6', B_1477, '#skF_6', D_1479)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10562, c_11872])).
% 8.60/3.15  tff(c_10558, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_8218])).
% 8.60/3.15  tff(c_10585, plain, (k1_tarski('#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10559, c_10558])).
% 8.60/3.15  tff(c_11255, plain, (![D_1347, A_1350, B_1349, C_1348, E_1346]: (k4_enumset1(A_1350, A_1350, B_1349, C_1348, D_1347, E_1346)=k3_enumset1(A_1350, B_1349, C_1348, D_1347, E_1346))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.60/3.15  tff(c_11296, plain, (![A_1354, E_1355, B_1356, C_1357, D_1353]: (r2_hidden(D_1353, k3_enumset1(A_1354, B_1356, C_1357, D_1353, E_1355)))), inference(superposition, [status(thm), theory('equality')], [c_11255, c_40])).
% 8.60/3.15  tff(c_11300, plain, (![C_1358, A_1359, B_1360, D_1361]: (r2_hidden(C_1358, k2_enumset1(A_1359, B_1360, C_1358, D_1361)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_11296])).
% 8.60/3.15  tff(c_11328, plain, (![B_1364, A_1365, C_1366]: (r2_hidden(B_1364, k1_enumset1(A_1365, B_1364, C_1366)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_11300])).
% 8.60/3.15  tff(c_11332, plain, (![A_1367, B_1368]: (r2_hidden(A_1367, k2_tarski(A_1367, B_1368)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_11328])).
% 8.60/3.15  tff(c_11336, plain, (![A_1369]: (r2_hidden(A_1369, k1_tarski(A_1369)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_11332])).
% 8.60/3.15  tff(c_11339, plain, (r2_hidden('#skF_3', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10585, c_11336])).
% 8.60/3.15  tff(c_10622, plain, (![A_1246]: (k9_relat_1('#skF_6', A_1246)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10559, c_10559, c_96])).
% 8.60/3.15  tff(c_10628, plain, (![B_53]: (k11_relat_1('#skF_6', B_53)='#skF_6' | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10622, c_84])).
% 8.60/3.15  tff(c_10640, plain, (![B_53]: (k11_relat_1('#skF_6', B_53)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_10628])).
% 8.60/3.15  tff(c_10711, plain, (![C_1271, A_1272, B_1273]: (v4_relat_1(C_1271, A_1272) | ~m1_subset_1(C_1271, k1_zfmisc_1(k2_zfmisc_1(A_1272, B_1273))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.60/3.15  tff(c_10776, plain, (![A_1286, A_1287, B_1288]: (v4_relat_1(A_1286, A_1287) | ~r1_tarski(A_1286, k2_zfmisc_1(A_1287, B_1288)))), inference(resolution, [status(thm)], [c_80, c_10711])).
% 8.60/3.15  tff(c_10793, plain, (![A_1287, B_1288]: (v4_relat_1(k2_zfmisc_1(A_1287, B_1288), A_1287))), inference(resolution, [status(thm)], [c_6, c_10776])).
% 8.60/3.15  tff(c_10906, plain, (![B_1310, A_1311]: (r1_tarski(k1_relat_1(B_1310), A_1311) | ~v4_relat_1(B_1310, A_1311) | ~v1_relat_1(B_1310))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.60/3.15  tff(c_10561, plain, (![A_3]: (A_3='#skF_6' | ~r1_tarski(A_3, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_10559, c_10559, c_208])).
% 8.60/3.15  tff(c_10938, plain, (![B_1312]: (k1_relat_1(B_1312)='#skF_6' | ~v4_relat_1(B_1312, '#skF_6') | ~v1_relat_1(B_1312))), inference(resolution, [status(thm)], [c_10906, c_10561])).
% 8.60/3.15  tff(c_10942, plain, (![B_1288]: (k1_relat_1(k2_zfmisc_1('#skF_6', B_1288))='#skF_6' | ~v1_relat_1(k2_zfmisc_1('#skF_6', B_1288)))), inference(resolution, [status(thm)], [c_10793, c_10938])).
% 8.60/3.15  tff(c_10953, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_10565, c_10942])).
% 8.60/3.15  tff(c_11395, plain, (![B_1411, A_1412]: (k1_tarski(k1_funct_1(B_1411, A_1412))=k11_relat_1(B_1411, A_1412) | ~r2_hidden(A_1412, k1_relat_1(B_1411)) | ~v1_funct_1(B_1411) | ~v1_relat_1(B_1411))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.60/3.15  tff(c_11398, plain, (![A_1412]: (k1_tarski(k1_funct_1('#skF_6', A_1412))=k11_relat_1('#skF_6', A_1412) | ~r2_hidden(A_1412, '#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10953, c_11395])).
% 8.60/3.15  tff(c_11407, plain, (![A_1418]: (k1_tarski(k1_funct_1('#skF_6', A_1418))='#skF_6' | ~r2_hidden(A_1418, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_242, c_118, c_10640, c_11398])).
% 8.60/3.15  tff(c_10587, plain, (~r1_tarski(k7_relset_1('#skF_6', '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_10585, c_110])).
% 8.60/3.15  tff(c_11419, plain, (~r1_tarski(k7_relset_1('#skF_6', '#skF_4', '#skF_6', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_3', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_11407, c_10587])).
% 8.60/3.15  tff(c_11428, plain, (~r1_tarski(k7_relset_1('#skF_6', '#skF_4', '#skF_6', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11339, c_11419])).
% 8.60/3.15  tff(c_11879, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11877, c_11428])).
% 8.60/3.15  tff(c_11883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10566, c_11879])).
% 8.60/3.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.60/3.15  
% 8.60/3.15  Inference rules
% 8.60/3.15  ----------------------
% 8.60/3.15  #Ref     : 0
% 8.60/3.15  #Sup     : 2459
% 8.60/3.15  #Fact    : 0
% 8.60/3.15  #Define  : 0
% 8.60/3.15  #Split   : 38
% 8.60/3.15  #Chain   : 0
% 8.60/3.15  #Close   : 0
% 8.60/3.15  
% 8.60/3.15  Ordering : KBO
% 8.60/3.15  
% 8.60/3.15  Simplification rules
% 8.60/3.15  ----------------------
% 8.60/3.15  #Subsume      : 402
% 8.60/3.15  #Demod        : 2697
% 8.60/3.15  #Tautology    : 1396
% 8.60/3.15  #SimpNegUnit  : 65
% 8.60/3.15  #BackRed      : 314
% 8.60/3.15  
% 8.60/3.15  #Partial instantiations: 0
% 8.60/3.15  #Strategies tried      : 1
% 8.60/3.15  
% 8.60/3.15  Timing (in seconds)
% 8.60/3.15  ----------------------
% 8.60/3.15  Preprocessing        : 0.38
% 8.60/3.15  Parsing              : 0.18
% 8.60/3.15  CNF conversion       : 0.03
% 8.60/3.15  Main loop            : 1.93
% 8.60/3.15  Inferencing          : 0.59
% 8.60/3.15  Reduction            : 0.73
% 8.60/3.15  Demodulation         : 0.54
% 8.60/3.15  BG Simplification    : 0.06
% 8.60/3.15  Subsumption          : 0.42
% 8.60/3.15  Abstraction          : 0.07
% 8.60/3.15  MUC search           : 0.00
% 8.60/3.15  Cooper               : 0.00
% 8.60/3.15  Total                : 2.40
% 8.60/3.15  Index Insertion      : 0.00
% 8.60/3.15  Index Deletion       : 0.00
% 8.60/3.15  Index Matching       : 0.00
% 8.60/3.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
