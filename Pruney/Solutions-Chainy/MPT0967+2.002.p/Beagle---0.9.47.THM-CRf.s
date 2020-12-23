%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:13 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :  238 (2741 expanded)
%              Number of leaves         :   45 ( 887 expanded)
%              Depth                    :   17
%              Number of atoms          :  437 (7515 expanded)
%              Number of equality atoms :  139 (2112 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_177,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v5_relat_1(C,A) )
         => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_147,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_157,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_88,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_34,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_86,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_202,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_205,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_86,c_202])).

tff(c_208,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_205])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_6379,plain,(
    ! [C_622,B_623,A_624] :
      ( v5_relat_1(C_622,B_623)
      | ~ m1_subset_1(C_622,k1_zfmisc_1(k2_zfmisc_1(A_624,B_623))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6389,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_6379])).

tff(c_6477,plain,(
    ! [C_639,B_640,A_641] :
      ( v5_relat_1(C_639,B_640)
      | ~ v5_relat_1(C_639,A_641)
      | ~ v1_relat_1(C_639)
      | ~ r1_tarski(A_641,B_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6483,plain,(
    ! [B_640] :
      ( v5_relat_1('#skF_6',B_640)
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_4',B_640) ) ),
    inference(resolution,[status(thm)],[c_6389,c_6477])).

tff(c_6491,plain,(
    ! [B_642] :
      ( v5_relat_1('#skF_6',B_642)
      | ~ r1_tarski('#skF_4',B_642) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_6483])).

tff(c_36,plain,(
    ! [C_23,B_21,A_20] :
      ( v5_relat_1(C_23,B_21)
      | ~ v5_relat_1(C_23,A_20)
      | ~ v1_relat_1(C_23)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6493,plain,(
    ! [B_21,B_642] :
      ( v5_relat_1('#skF_6',B_21)
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski(B_642,B_21)
      | ~ r1_tarski('#skF_4',B_642) ) ),
    inference(resolution,[status(thm)],[c_6491,c_36])).

tff(c_6505,plain,(
    ! [B_643,B_644] :
      ( v5_relat_1('#skF_6',B_643)
      | ~ r1_tarski(B_644,B_643)
      | ~ r1_tarski('#skF_4',B_644) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_6493])).

tff(c_6515,plain,
    ( v5_relat_1('#skF_6','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_6505])).

tff(c_6522,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6515])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6367,plain,(
    ! [C_617,A_618,B_619] :
      ( v4_relat_1(C_617,A_618)
      | ~ m1_subset_1(C_617,k1_zfmisc_1(k2_zfmisc_1(A_618,B_619))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6377,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_6367])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6845,plain,(
    ! [C_685,A_686,B_687] :
      ( m1_subset_1(C_685,k1_zfmisc_1(k2_zfmisc_1(A_686,B_687)))
      | ~ r1_tarski(k2_relat_1(C_685),B_687)
      | ~ r1_tarski(k1_relat_1(C_685),A_686)
      | ~ v1_relat_1(C_685) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_90,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_18,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    ! [A_24] :
      ( k1_relat_1(A_24) = k1_xboole_0
      | k2_relat_1(A_24) != k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_216,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_208,c_42])).

tff(c_232,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_249,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_259,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_249])).

tff(c_1136,plain,(
    ! [C_177,B_178,A_179] :
      ( v5_relat_1(C_177,B_178)
      | ~ v5_relat_1(C_177,A_179)
      | ~ v1_relat_1(C_177)
      | ~ r1_tarski(A_179,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1142,plain,(
    ! [B_178] :
      ( v5_relat_1('#skF_6',B_178)
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_4',B_178) ) ),
    inference(resolution,[status(thm)],[c_259,c_1136])).

tff(c_1150,plain,(
    ! [B_180] :
      ( v5_relat_1('#skF_6',B_180)
      | ~ r1_tarski('#skF_4',B_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_1142])).

tff(c_1152,plain,(
    ! [B_21,B_180] :
      ( v5_relat_1('#skF_6',B_21)
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski(B_180,B_21)
      | ~ r1_tarski('#skF_4',B_180) ) ),
    inference(resolution,[status(thm)],[c_1150,c_36])).

tff(c_1164,plain,(
    ! [B_181,B_182] :
      ( v5_relat_1('#skF_6',B_181)
      | ~ r1_tarski(B_182,B_181)
      | ~ r1_tarski('#skF_4',B_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_1152])).

tff(c_1174,plain,
    ( v5_relat_1('#skF_6','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_1164])).

tff(c_1181,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1174])).

tff(c_82,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_115,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_88,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1333,plain,(
    ! [A_199,B_200,C_201] :
      ( k1_relset_1(A_199,B_200,C_201) = k1_relat_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1343,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_1333])).

tff(c_1707,plain,(
    ! [B_240,A_241,C_242] :
      ( k1_xboole_0 = B_240
      | k1_relset_1(A_241,B_240,C_242) = A_241
      | ~ v1_funct_2(C_242,A_241,B_240)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_241,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1716,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_1707])).

tff(c_1727,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1343,c_1716])).

tff(c_1728,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_1727])).

tff(c_1659,plain,(
    ! [C_235,A_236,B_237] :
      ( m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237)))
      | ~ r1_tarski(k2_relat_1(C_235),B_237)
      | ~ r1_tarski(k1_relat_1(C_235),A_236)
      | ~ v1_relat_1(C_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2627,plain,(
    ! [A_320,B_321,C_322] :
      ( k1_relset_1(A_320,B_321,C_322) = k1_relat_1(C_322)
      | ~ r1_tarski(k2_relat_1(C_322),B_321)
      | ~ r1_tarski(k1_relat_1(C_322),A_320)
      | ~ v1_relat_1(C_322) ) ),
    inference(resolution,[status(thm)],[c_1659,c_52])).

tff(c_2857,plain,(
    ! [A_336,A_337,B_338] :
      ( k1_relset_1(A_336,A_337,B_338) = k1_relat_1(B_338)
      | ~ r1_tarski(k1_relat_1(B_338),A_336)
      | ~ v5_relat_1(B_338,A_337)
      | ~ v1_relat_1(B_338) ) ),
    inference(resolution,[status(thm)],[c_32,c_2627])).

tff(c_2859,plain,(
    ! [A_336,A_337] :
      ( k1_relset_1(A_336,A_337,'#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_3',A_336)
      | ~ v5_relat_1('#skF_6',A_337)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1728,c_2857])).

tff(c_2873,plain,(
    ! [A_339,A_340] :
      ( k1_relset_1(A_339,A_340,'#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_339)
      | ~ v5_relat_1('#skF_6',A_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_1728,c_2859])).

tff(c_2878,plain,(
    ! [A_341] :
      ( k1_relset_1('#skF_3',A_341,'#skF_6') = '#skF_3'
      | ~ v5_relat_1('#skF_6',A_341) ) ),
    inference(resolution,[status(thm)],[c_8,c_2873])).

tff(c_2908,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1181,c_2878])).

tff(c_54,plain,(
    ! [C_35,A_33,B_34] :
      ( m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ r1_tarski(k2_relat_1(C_35),B_34)
      | ~ r1_tarski(k1_relat_1(C_35),A_33)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1819,plain,(
    ! [B_245,C_246,A_247] :
      ( k1_xboole_0 = B_245
      | v1_funct_2(C_246,A_247,B_245)
      | k1_relset_1(A_247,B_245,C_246) != A_247
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_247,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_3042,plain,(
    ! [B_349,C_350,A_351] :
      ( k1_xboole_0 = B_349
      | v1_funct_2(C_350,A_351,B_349)
      | k1_relset_1(A_351,B_349,C_350) != A_351
      | ~ r1_tarski(k2_relat_1(C_350),B_349)
      | ~ r1_tarski(k1_relat_1(C_350),A_351)
      | ~ v1_relat_1(C_350) ) ),
    inference(resolution,[status(thm)],[c_54,c_1819])).

tff(c_4473,plain,(
    ! [A_463,B_464,A_465] :
      ( k1_xboole_0 = A_463
      | v1_funct_2(B_464,A_465,A_463)
      | k1_relset_1(A_465,A_463,B_464) != A_465
      | ~ r1_tarski(k1_relat_1(B_464),A_465)
      | ~ v5_relat_1(B_464,A_463)
      | ~ v1_relat_1(B_464) ) ),
    inference(resolution,[status(thm)],[c_32,c_3042])).

tff(c_4475,plain,(
    ! [A_463,A_465] :
      ( k1_xboole_0 = A_463
      | v1_funct_2('#skF_6',A_465,A_463)
      | k1_relset_1(A_465,A_463,'#skF_6') != A_465
      | ~ r1_tarski('#skF_3',A_465)
      | ~ v5_relat_1('#skF_6',A_463)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1728,c_4473])).

tff(c_4489,plain,(
    ! [A_466,A_467] :
      ( k1_xboole_0 = A_466
      | v1_funct_2('#skF_6',A_467,A_466)
      | k1_relset_1(A_467,A_466,'#skF_6') != A_467
      | ~ r1_tarski('#skF_3',A_467)
      | ~ v5_relat_1('#skF_6',A_466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_4475])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_92,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_80])).

tff(c_231,plain,(
    ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_4497,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_4489,c_231])).

tff(c_4504,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_8,c_2908,c_4497])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2100,plain,(
    ! [C_269,A_270] :
      ( m1_subset_1(C_269,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_269),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_269),A_270)
      | ~ v1_relat_1(C_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1659])).

tff(c_2123,plain,(
    ! [B_275,A_276] :
      ( m1_subset_1(B_275,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(B_275),A_276)
      | ~ v5_relat_1(B_275,k1_xboole_0)
      | ~ v1_relat_1(B_275) ) ),
    inference(resolution,[status(thm)],[c_32,c_2100])).

tff(c_2126,plain,(
    ! [A_276] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',A_276)
      | ~ v5_relat_1('#skF_6',k1_xboole_0)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1728,c_2123])).

tff(c_2137,plain,(
    ! [A_276] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_3',A_276)
      | ~ v5_relat_1('#skF_6',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_2126])).

tff(c_2326,plain,(
    ~ v5_relat_1('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2137])).

tff(c_4551,plain,(
    ~ v5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4504,c_2326])).

tff(c_4609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_4551])).

tff(c_4611,plain,(
    v5_relat_1('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2137])).

tff(c_301,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(k2_relat_1(B_89),A_90)
      | ~ v5_relat_1(B_89,A_90)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_189,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_200,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_189])).

tff(c_311,plain,(
    ! [B_89] :
      ( k2_relat_1(B_89) = k1_xboole_0
      | ~ v5_relat_1(B_89,k1_xboole_0)
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_301,c_200])).

tff(c_4623,plain,
    ( k2_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4611,c_311])).

tff(c_4638,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_4623])).

tff(c_4640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_4638])).

tff(c_4641,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_4642,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_5604,plain,(
    ! [A_560] :
      ( m1_subset_1(A_560,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_560),k2_relat_1(A_560))))
      | ~ v1_funct_1(A_560)
      | ~ v1_relat_1(A_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_5622,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k1_xboole_0)))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4642,c_5604])).

tff(c_5641,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_90,c_18,c_4641,c_5622])).

tff(c_20,plain,(
    ! [B_9,A_7] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5657,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5641,c_20])).

tff(c_5667,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5657])).

tff(c_12,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5676,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_5667,c_12])).

tff(c_5693,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5676,c_4641])).

tff(c_5745,plain,(
    ! [A_561,B_562,C_563] :
      ( k1_relset_1(A_561,B_562,C_563) = k1_relat_1(C_563)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(A_561,B_562))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5753,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_5745])).

tff(c_5788,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5693,c_5753])).

tff(c_6009,plain,(
    ! [A_588,B_589,C_590] :
      ( r2_hidden('#skF_1'(A_588,B_589,C_590),B_589)
      | k1_relset_1(B_589,A_588,C_590) = B_589
      | ~ m1_subset_1(C_590,k1_zfmisc_1(k2_zfmisc_1(B_589,A_588))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_6019,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3','#skF_6'),'#skF_3')
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_86,c_6009])).

tff(c_6023,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3','#skF_6'),'#skF_3')
    | '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5788,c_6019])).

tff(c_6024,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6023])).

tff(c_6049,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6024,c_5667])).

tff(c_5698,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_6',B_6) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5676,c_5676,c_18])).

tff(c_6041,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6024,c_6024,c_5698])).

tff(c_150,plain,(
    ! [B_63,A_64] :
      ( v1_xboole_0(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_154,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_86,c_150])).

tff(c_155,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_6206,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6041,c_155])).

tff(c_6209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6049,c_6206])).

tff(c_6211,plain,(
    '#skF_6' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6023])).

tff(c_5701,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5676,c_115])).

tff(c_72,plain,(
    ! [B_50,A_49,C_51] :
      ( k1_xboole_0 = B_50
      | k1_relset_1(A_49,B_50,C_51) = A_49
      | ~ v1_funct_2(C_51,A_49,B_50)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_6324,plain,(
    ! [B_611,A_612,C_613] :
      ( B_611 = '#skF_6'
      | k1_relset_1(A_612,B_611,C_613) = A_612
      | ~ v1_funct_2(C_613,A_612,B_611)
      | ~ m1_subset_1(C_613,k1_zfmisc_1(k2_zfmisc_1(A_612,B_611))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5676,c_72])).

tff(c_6339,plain,
    ( '#skF_6' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_6324])).

tff(c_6345,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5788,c_6339])).

tff(c_6347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6211,c_5701,c_6345])).

tff(c_6348,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_6857,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6845,c_6348])).

tff(c_6875,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_6857])).

tff(c_6880,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6875])).

tff(c_6883,plain,
    ( ~ v4_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_6880])).

tff(c_6887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_6377,c_6883])).

tff(c_6888,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_6875])).

tff(c_6907,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_6888])).

tff(c_6911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_6522,c_6907])).

tff(c_6912,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_6921,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6912,c_12])).

tff(c_6941,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6921,c_115])).

tff(c_6913,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_7642,plain,(
    ! [A_768] :
      ( A_768 = '#skF_6'
      | ~ v1_xboole_0(A_768) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6921,c_12])).

tff(c_7649,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6913,c_7642])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( k1_xboole_0 = B_6
      | k1_xboole_0 = A_5
      | k2_zfmisc_1(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_7726,plain,(
    ! [B_774,A_775] :
      ( B_774 = '#skF_6'
      | A_775 = '#skF_6'
      | k2_zfmisc_1(A_775,B_774) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6921,c_6921,c_6921,c_14])).

tff(c_7729,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7649,c_7726])).

tff(c_7738,plain,(
    '#skF_6' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6941,c_7729])).

tff(c_7681,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7649,c_86])).

tff(c_7745,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7738,c_7738,c_7681])).

tff(c_6938,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_6',B_6) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6921,c_6921,c_18])).

tff(c_7749,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7738,c_7738,c_6938])).

tff(c_6985,plain,(
    ! [A_693] :
      ( A_693 = '#skF_6'
      | ~ v1_xboole_0(A_693) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6921,c_12])).

tff(c_6992,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6913,c_6985])).

tff(c_6968,plain,(
    ! [B_6,A_5] :
      ( B_6 = '#skF_6'
      | A_5 = '#skF_6'
      | k2_zfmisc_1(A_5,B_6) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6921,c_6921,c_6921,c_14])).

tff(c_7024,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_6992,c_6968])).

tff(c_7031,plain,(
    '#skF_6' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6941,c_7024])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6944,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6921,c_6921,c_40])).

tff(c_7040,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7031,c_7031,c_6944])).

tff(c_7019,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6992,c_86])).

tff(c_7077,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7031,c_7031,c_7019])).

tff(c_7035,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_3',B_6) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7031,c_7031,c_6938])).

tff(c_7458,plain,(
    ! [A_748,B_749,C_750] :
      ( k1_relset_1(A_748,B_749,C_750) = k1_relat_1(C_750)
      | ~ m1_subset_1(C_750,k1_zfmisc_1(k2_zfmisc_1(A_748,B_749))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_7481,plain,(
    ! [B_754,C_755] :
      ( k1_relset_1('#skF_3',B_754,C_755) = k1_relat_1(C_755)
      | ~ m1_subset_1(C_755,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7035,c_7458])).

tff(c_7483,plain,(
    ! [B_754] : k1_relset_1('#skF_3',B_754,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7077,c_7481])).

tff(c_7485,plain,(
    ! [B_754] : k1_relset_1('#skF_3',B_754,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7040,c_7483])).

tff(c_7044,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7031,c_6921])).

tff(c_66,plain,(
    ! [C_51,B_50] :
      ( v1_funct_2(C_51,k1_xboole_0,B_50)
      | k1_relset_1(k1_xboole_0,B_50,C_51) != k1_xboole_0
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_94,plain,(
    ! [C_51,B_50] :
      ( v1_funct_2(C_51,k1_xboole_0,B_50)
      | k1_relset_1(k1_xboole_0,B_50,C_51) != k1_xboole_0
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_66])).

tff(c_7615,plain,(
    ! [C_765,B_766] :
      ( v1_funct_2(C_765,'#skF_3',B_766)
      | k1_relset_1('#skF_3',B_766,C_765) != '#skF_3'
      | ~ m1_subset_1(C_765,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7044,c_7044,c_7044,c_7044,c_94])).

tff(c_7617,plain,(
    ! [B_766] :
      ( v1_funct_2('#skF_3','#skF_3',B_766)
      | k1_relset_1('#skF_3',B_766,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_7077,c_7615])).

tff(c_7620,plain,(
    ! [B_766] : v1_funct_2('#skF_3','#skF_3',B_766) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7485,c_7617])).

tff(c_6953,plain,(
    ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_7039,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7031,c_6953])).

tff(c_7625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7620,c_7039])).

tff(c_7626,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_7747,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7738,c_7626])).

tff(c_7872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7745,c_7749,c_7747])).

tff(c_7874,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_7873,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_7884,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7874,c_7873])).

tff(c_7877,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7873,c_7873,c_40])).

tff(c_7899,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7884,c_7884,c_7877])).

tff(c_7879,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7873,c_2])).

tff(c_7895,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7884,c_7879])).

tff(c_7916,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7874,c_7874,c_16])).

tff(c_7889,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7884,c_86])).

tff(c_7926,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7916,c_7889])).

tff(c_8000,plain,(
    ! [B_800,A_801] :
      ( v1_xboole_0(B_800)
      | ~ m1_subset_1(B_800,k1_zfmisc_1(A_801))
      | ~ v1_xboole_0(A_801) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8003,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_7926,c_8000])).

tff(c_8006,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7895,c_8003])).

tff(c_7875,plain,(
    ! [A_4] :
      ( A_4 = '#skF_3'
      | ~ v1_xboole_0(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7873,c_12])).

tff(c_7909,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ v1_xboole_0(A_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7884,c_7875])).

tff(c_8014,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8006,c_7909])).

tff(c_8024,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8014,c_7926])).

tff(c_7933,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7874,c_7874,c_18])).

tff(c_8292,plain,(
    ! [A_844,B_845,C_846] :
      ( k1_relset_1(A_844,B_845,C_846) = k1_relat_1(C_846)
      | ~ m1_subset_1(C_846,k1_zfmisc_1(k2_zfmisc_1(A_844,B_845))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8299,plain,(
    ! [B_847,C_848] :
      ( k1_relset_1('#skF_4',B_847,C_848) = k1_relat_1(C_848)
      | ~ m1_subset_1(C_848,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7933,c_8292])).

tff(c_8301,plain,(
    ! [B_847] : k1_relset_1('#skF_4',B_847,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8024,c_8299])).

tff(c_8303,plain,(
    ! [B_847] : k1_relset_1('#skF_4',B_847,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7899,c_8301])).

tff(c_8512,plain,(
    ! [C_865,B_866] :
      ( v1_funct_2(C_865,'#skF_4',B_866)
      | k1_relset_1('#skF_4',B_866,C_865) != '#skF_4'
      | ~ m1_subset_1(C_865,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7874,c_7874,c_7874,c_7874,c_94])).

tff(c_8514,plain,(
    ! [B_866] :
      ( v1_funct_2('#skF_4','#skF_4',B_866)
      | k1_relset_1('#skF_4',B_866,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_8024,c_8512])).

tff(c_8517,plain,(
    ! [B_866] : v1_funct_2('#skF_4','#skF_4',B_866) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8303,c_8514])).

tff(c_8016,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7884,c_7926,c_7933,c_7884,c_92])).

tff(c_8022,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8014,c_8016])).

tff(c_8521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8517,c_8022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:28:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.02/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.54  
% 7.43/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4
% 7.43/2.54  
% 7.43/2.54  %Foreground sorts:
% 7.43/2.54  
% 7.43/2.54  
% 7.43/2.54  %Background operators:
% 7.43/2.54  
% 7.43/2.54  
% 7.43/2.54  %Foreground operators:
% 7.43/2.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.43/2.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.43/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.43/2.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.43/2.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.43/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.43/2.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.43/2.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.43/2.54  tff('#skF_5', type, '#skF_5': $i).
% 7.43/2.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.43/2.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.43/2.54  tff('#skF_6', type, '#skF_6': $i).
% 7.43/2.54  tff('#skF_3', type, '#skF_3': $i).
% 7.43/2.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.43/2.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.43/2.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.43/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.43/2.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.43/2.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.43/2.54  tff('#skF_4', type, '#skF_4': $i).
% 7.43/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.43/2.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.43/2.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.43/2.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.43/2.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.43/2.54  
% 7.43/2.57  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.43/2.57  tff(f_177, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 7.43/2.57  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.43/2.57  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.43/2.57  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.43/2.57  tff(f_85, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t218_relat_1)).
% 7.43/2.57  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.43/2.57  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.43/2.57  tff(f_117, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.43/2.57  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.43/2.57  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.43/2.57  tff(f_94, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 7.43/2.57  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.43/2.57  tff(f_147, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.43/2.57  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.43/2.57  tff(f_157, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.43/2.57  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 7.43/2.57  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 7.43/2.57  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 7.43/2.57  tff(f_88, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.43/2.57  tff(c_34, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.43/2.57  tff(c_86, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.43/2.57  tff(c_202, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.43/2.57  tff(c_205, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_202])).
% 7.43/2.57  tff(c_208, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_205])).
% 7.43/2.57  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.43/2.57  tff(c_84, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.43/2.57  tff(c_6379, plain, (![C_622, B_623, A_624]: (v5_relat_1(C_622, B_623) | ~m1_subset_1(C_622, k1_zfmisc_1(k2_zfmisc_1(A_624, B_623))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.43/2.57  tff(c_6389, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_6379])).
% 7.43/2.57  tff(c_6477, plain, (![C_639, B_640, A_641]: (v5_relat_1(C_639, B_640) | ~v5_relat_1(C_639, A_641) | ~v1_relat_1(C_639) | ~r1_tarski(A_641, B_640))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.43/2.57  tff(c_6483, plain, (![B_640]: (v5_relat_1('#skF_6', B_640) | ~v1_relat_1('#skF_6') | ~r1_tarski('#skF_4', B_640))), inference(resolution, [status(thm)], [c_6389, c_6477])).
% 7.43/2.57  tff(c_6491, plain, (![B_642]: (v5_relat_1('#skF_6', B_642) | ~r1_tarski('#skF_4', B_642))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_6483])).
% 7.43/2.57  tff(c_36, plain, (![C_23, B_21, A_20]: (v5_relat_1(C_23, B_21) | ~v5_relat_1(C_23, A_20) | ~v1_relat_1(C_23) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.43/2.57  tff(c_6493, plain, (![B_21, B_642]: (v5_relat_1('#skF_6', B_21) | ~v1_relat_1('#skF_6') | ~r1_tarski(B_642, B_21) | ~r1_tarski('#skF_4', B_642))), inference(resolution, [status(thm)], [c_6491, c_36])).
% 7.43/2.57  tff(c_6505, plain, (![B_643, B_644]: (v5_relat_1('#skF_6', B_643) | ~r1_tarski(B_644, B_643) | ~r1_tarski('#skF_4', B_644))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_6493])).
% 7.43/2.57  tff(c_6515, plain, (v5_relat_1('#skF_6', '#skF_5') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_6505])).
% 7.43/2.57  tff(c_6522, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6515])).
% 7.43/2.57  tff(c_32, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.43/2.57  tff(c_6367, plain, (![C_617, A_618, B_619]: (v4_relat_1(C_617, A_618) | ~m1_subset_1(C_617, k1_zfmisc_1(k2_zfmisc_1(A_618, B_619))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.43/2.57  tff(c_6377, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_86, c_6367])).
% 7.43/2.57  tff(c_28, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.43/2.57  tff(c_6845, plain, (![C_685, A_686, B_687]: (m1_subset_1(C_685, k1_zfmisc_1(k2_zfmisc_1(A_686, B_687))) | ~r1_tarski(k2_relat_1(C_685), B_687) | ~r1_tarski(k1_relat_1(C_685), A_686) | ~v1_relat_1(C_685))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.43/2.57  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.43/2.57  tff(c_90, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.43/2.57  tff(c_18, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.43/2.57  tff(c_42, plain, (![A_24]: (k1_relat_1(A_24)=k1_xboole_0 | k2_relat_1(A_24)!=k1_xboole_0 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.43/2.57  tff(c_216, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_208, c_42])).
% 7.43/2.57  tff(c_232, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_216])).
% 7.43/2.57  tff(c_249, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.43/2.57  tff(c_259, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_249])).
% 7.43/2.57  tff(c_1136, plain, (![C_177, B_178, A_179]: (v5_relat_1(C_177, B_178) | ~v5_relat_1(C_177, A_179) | ~v1_relat_1(C_177) | ~r1_tarski(A_179, B_178))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.43/2.57  tff(c_1142, plain, (![B_178]: (v5_relat_1('#skF_6', B_178) | ~v1_relat_1('#skF_6') | ~r1_tarski('#skF_4', B_178))), inference(resolution, [status(thm)], [c_259, c_1136])).
% 7.43/2.57  tff(c_1150, plain, (![B_180]: (v5_relat_1('#skF_6', B_180) | ~r1_tarski('#skF_4', B_180))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_1142])).
% 7.43/2.57  tff(c_1152, plain, (![B_21, B_180]: (v5_relat_1('#skF_6', B_21) | ~v1_relat_1('#skF_6') | ~r1_tarski(B_180, B_21) | ~r1_tarski('#skF_4', B_180))), inference(resolution, [status(thm)], [c_1150, c_36])).
% 7.43/2.57  tff(c_1164, plain, (![B_181, B_182]: (v5_relat_1('#skF_6', B_181) | ~r1_tarski(B_182, B_181) | ~r1_tarski('#skF_4', B_182))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_1152])).
% 7.43/2.57  tff(c_1174, plain, (v5_relat_1('#skF_6', '#skF_5') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_1164])).
% 7.43/2.57  tff(c_1181, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1174])).
% 7.43/2.57  tff(c_82, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.43/2.57  tff(c_115, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_82])).
% 7.43/2.57  tff(c_88, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.43/2.57  tff(c_1333, plain, (![A_199, B_200, C_201]: (k1_relset_1(A_199, B_200, C_201)=k1_relat_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.43/2.57  tff(c_1343, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_1333])).
% 7.43/2.57  tff(c_1707, plain, (![B_240, A_241, C_242]: (k1_xboole_0=B_240 | k1_relset_1(A_241, B_240, C_242)=A_241 | ~v1_funct_2(C_242, A_241, B_240) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_241, B_240))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.43/2.57  tff(c_1716, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_1707])).
% 7.43/2.57  tff(c_1727, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1343, c_1716])).
% 7.43/2.57  tff(c_1728, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_115, c_1727])).
% 7.43/2.57  tff(c_1659, plain, (![C_235, A_236, B_237]: (m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))) | ~r1_tarski(k2_relat_1(C_235), B_237) | ~r1_tarski(k1_relat_1(C_235), A_236) | ~v1_relat_1(C_235))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.43/2.57  tff(c_52, plain, (![A_30, B_31, C_32]: (k1_relset_1(A_30, B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.43/2.57  tff(c_2627, plain, (![A_320, B_321, C_322]: (k1_relset_1(A_320, B_321, C_322)=k1_relat_1(C_322) | ~r1_tarski(k2_relat_1(C_322), B_321) | ~r1_tarski(k1_relat_1(C_322), A_320) | ~v1_relat_1(C_322))), inference(resolution, [status(thm)], [c_1659, c_52])).
% 7.43/2.57  tff(c_2857, plain, (![A_336, A_337, B_338]: (k1_relset_1(A_336, A_337, B_338)=k1_relat_1(B_338) | ~r1_tarski(k1_relat_1(B_338), A_336) | ~v5_relat_1(B_338, A_337) | ~v1_relat_1(B_338))), inference(resolution, [status(thm)], [c_32, c_2627])).
% 7.43/2.57  tff(c_2859, plain, (![A_336, A_337]: (k1_relset_1(A_336, A_337, '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski('#skF_3', A_336) | ~v5_relat_1('#skF_6', A_337) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1728, c_2857])).
% 7.43/2.57  tff(c_2873, plain, (![A_339, A_340]: (k1_relset_1(A_339, A_340, '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_339) | ~v5_relat_1('#skF_6', A_340))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_1728, c_2859])).
% 7.43/2.57  tff(c_2878, plain, (![A_341]: (k1_relset_1('#skF_3', A_341, '#skF_6')='#skF_3' | ~v5_relat_1('#skF_6', A_341))), inference(resolution, [status(thm)], [c_8, c_2873])).
% 7.43/2.57  tff(c_2908, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_1181, c_2878])).
% 7.43/2.57  tff(c_54, plain, (![C_35, A_33, B_34]: (m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~r1_tarski(k2_relat_1(C_35), B_34) | ~r1_tarski(k1_relat_1(C_35), A_33) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_117])).
% 7.43/2.57  tff(c_1819, plain, (![B_245, C_246, A_247]: (k1_xboole_0=B_245 | v1_funct_2(C_246, A_247, B_245) | k1_relset_1(A_247, B_245, C_246)!=A_247 | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_247, B_245))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.43/2.57  tff(c_3042, plain, (![B_349, C_350, A_351]: (k1_xboole_0=B_349 | v1_funct_2(C_350, A_351, B_349) | k1_relset_1(A_351, B_349, C_350)!=A_351 | ~r1_tarski(k2_relat_1(C_350), B_349) | ~r1_tarski(k1_relat_1(C_350), A_351) | ~v1_relat_1(C_350))), inference(resolution, [status(thm)], [c_54, c_1819])).
% 7.43/2.57  tff(c_4473, plain, (![A_463, B_464, A_465]: (k1_xboole_0=A_463 | v1_funct_2(B_464, A_465, A_463) | k1_relset_1(A_465, A_463, B_464)!=A_465 | ~r1_tarski(k1_relat_1(B_464), A_465) | ~v5_relat_1(B_464, A_463) | ~v1_relat_1(B_464))), inference(resolution, [status(thm)], [c_32, c_3042])).
% 7.43/2.57  tff(c_4475, plain, (![A_463, A_465]: (k1_xboole_0=A_463 | v1_funct_2('#skF_6', A_465, A_463) | k1_relset_1(A_465, A_463, '#skF_6')!=A_465 | ~r1_tarski('#skF_3', A_465) | ~v5_relat_1('#skF_6', A_463) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1728, c_4473])).
% 7.43/2.57  tff(c_4489, plain, (![A_466, A_467]: (k1_xboole_0=A_466 | v1_funct_2('#skF_6', A_467, A_466) | k1_relset_1(A_467, A_466, '#skF_6')!=A_467 | ~r1_tarski('#skF_3', A_467) | ~v5_relat_1('#skF_6', A_466))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_4475])).
% 7.43/2.57  tff(c_80, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_177])).
% 7.43/2.57  tff(c_92, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_80])).
% 7.43/2.57  tff(c_231, plain, (~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_92])).
% 7.43/2.57  tff(c_4497, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_3', '#skF_3') | ~v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_4489, c_231])).
% 7.43/2.57  tff(c_4504, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1181, c_8, c_2908, c_4497])).
% 7.43/2.57  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.43/2.57  tff(c_2100, plain, (![C_269, A_270]: (m1_subset_1(C_269, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_269), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_269), A_270) | ~v1_relat_1(C_269))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1659])).
% 7.43/2.57  tff(c_2123, plain, (![B_275, A_276]: (m1_subset_1(B_275, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(B_275), A_276) | ~v5_relat_1(B_275, k1_xboole_0) | ~v1_relat_1(B_275))), inference(resolution, [status(thm)], [c_32, c_2100])).
% 7.43/2.57  tff(c_2126, plain, (![A_276]: (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', A_276) | ~v5_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1728, c_2123])).
% 7.43/2.57  tff(c_2137, plain, (![A_276]: (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', A_276) | ~v5_relat_1('#skF_6', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_2126])).
% 7.43/2.57  tff(c_2326, plain, (~v5_relat_1('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2137])).
% 7.43/2.57  tff(c_4551, plain, (~v5_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4504, c_2326])).
% 7.43/2.57  tff(c_4609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1181, c_4551])).
% 7.43/2.57  tff(c_4611, plain, (v5_relat_1('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2137])).
% 7.43/2.57  tff(c_301, plain, (![B_89, A_90]: (r1_tarski(k2_relat_1(B_89), A_90) | ~v5_relat_1(B_89, A_90) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.43/2.57  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.43/2.57  tff(c_189, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.43/2.57  tff(c_200, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_189])).
% 7.43/2.57  tff(c_311, plain, (![B_89]: (k2_relat_1(B_89)=k1_xboole_0 | ~v5_relat_1(B_89, k1_xboole_0) | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_301, c_200])).
% 7.43/2.57  tff(c_4623, plain, (k2_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4611, c_311])).
% 7.43/2.57  tff(c_4638, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_208, c_4623])).
% 7.43/2.57  tff(c_4640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_4638])).
% 7.43/2.57  tff(c_4641, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_216])).
% 7.43/2.57  tff(c_4642, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_216])).
% 7.43/2.57  tff(c_5604, plain, (![A_560]: (m1_subset_1(A_560, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_560), k2_relat_1(A_560)))) | ~v1_funct_1(A_560) | ~v1_relat_1(A_560))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.43/2.57  tff(c_5622, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k1_xboole_0))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4642, c_5604])).
% 7.43/2.57  tff(c_5641, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_90, c_18, c_4641, c_5622])).
% 7.43/2.57  tff(c_20, plain, (![B_9, A_7]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.43/2.57  tff(c_5657, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_5641, c_20])).
% 7.43/2.57  tff(c_5667, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_5657])).
% 7.43/2.57  tff(c_12, plain, (![A_4]: (k1_xboole_0=A_4 | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.43/2.57  tff(c_5676, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_5667, c_12])).
% 7.43/2.57  tff(c_5693, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5676, c_4641])).
% 7.43/2.57  tff(c_5745, plain, (![A_561, B_562, C_563]: (k1_relset_1(A_561, B_562, C_563)=k1_relat_1(C_563) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(A_561, B_562))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.43/2.57  tff(c_5753, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_5745])).
% 7.43/2.57  tff(c_5788, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5693, c_5753])).
% 7.43/2.57  tff(c_6009, plain, (![A_588, B_589, C_590]: (r2_hidden('#skF_1'(A_588, B_589, C_590), B_589) | k1_relset_1(B_589, A_588, C_590)=B_589 | ~m1_subset_1(C_590, k1_zfmisc_1(k2_zfmisc_1(B_589, A_588))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.43/2.57  tff(c_6019, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3', '#skF_6'), '#skF_3') | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_86, c_6009])).
% 7.43/2.57  tff(c_6023, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3', '#skF_6'), '#skF_3') | '#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5788, c_6019])).
% 7.43/2.57  tff(c_6024, plain, ('#skF_6'='#skF_3'), inference(splitLeft, [status(thm)], [c_6023])).
% 7.43/2.57  tff(c_6049, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6024, c_5667])).
% 7.43/2.57  tff(c_5698, plain, (![B_6]: (k2_zfmisc_1('#skF_6', B_6)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5676, c_5676, c_18])).
% 7.43/2.57  tff(c_6041, plain, (![B_6]: (k2_zfmisc_1('#skF_3', B_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6024, c_6024, c_5698])).
% 7.43/2.57  tff(c_150, plain, (![B_63, A_64]: (v1_xboole_0(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.43/2.57  tff(c_154, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_150])).
% 7.43/2.57  tff(c_155, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_154])).
% 7.43/2.57  tff(c_6206, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6041, c_155])).
% 7.43/2.57  tff(c_6209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6049, c_6206])).
% 7.43/2.57  tff(c_6211, plain, ('#skF_6'!='#skF_3'), inference(splitRight, [status(thm)], [c_6023])).
% 7.43/2.57  tff(c_5701, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5676, c_115])).
% 7.43/2.57  tff(c_72, plain, (![B_50, A_49, C_51]: (k1_xboole_0=B_50 | k1_relset_1(A_49, B_50, C_51)=A_49 | ~v1_funct_2(C_51, A_49, B_50) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.43/2.57  tff(c_6324, plain, (![B_611, A_612, C_613]: (B_611='#skF_6' | k1_relset_1(A_612, B_611, C_613)=A_612 | ~v1_funct_2(C_613, A_612, B_611) | ~m1_subset_1(C_613, k1_zfmisc_1(k2_zfmisc_1(A_612, B_611))))), inference(demodulation, [status(thm), theory('equality')], [c_5676, c_72])).
% 7.43/2.57  tff(c_6339, plain, ('#skF_6'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_6324])).
% 7.43/2.57  tff(c_6345, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5788, c_6339])).
% 7.43/2.57  tff(c_6347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6211, c_5701, c_6345])).
% 7.43/2.57  tff(c_6348, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_92])).
% 7.43/2.57  tff(c_6857, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski(k1_relat_1('#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6845, c_6348])).
% 7.43/2.57  tff(c_6875, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_6857])).
% 7.43/2.57  tff(c_6880, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_6875])).
% 7.43/2.57  tff(c_6883, plain, (~v4_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_28, c_6880])).
% 7.43/2.57  tff(c_6887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_208, c_6377, c_6883])).
% 7.43/2.57  tff(c_6888, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_6875])).
% 7.43/2.57  tff(c_6907, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_6888])).
% 7.43/2.57  tff(c_6911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_208, c_6522, c_6907])).
% 7.43/2.57  tff(c_6912, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_154])).
% 7.43/2.57  tff(c_6921, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_6912, c_12])).
% 7.43/2.57  tff(c_6941, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6921, c_115])).
% 7.43/2.57  tff(c_6913, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_154])).
% 7.43/2.57  tff(c_7642, plain, (![A_768]: (A_768='#skF_6' | ~v1_xboole_0(A_768))), inference(demodulation, [status(thm), theory('equality')], [c_6921, c_12])).
% 7.43/2.57  tff(c_7649, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_6913, c_7642])).
% 7.43/2.57  tff(c_14, plain, (![B_6, A_5]: (k1_xboole_0=B_6 | k1_xboole_0=A_5 | k2_zfmisc_1(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.43/2.57  tff(c_7726, plain, (![B_774, A_775]: (B_774='#skF_6' | A_775='#skF_6' | k2_zfmisc_1(A_775, B_774)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6921, c_6921, c_6921, c_14])).
% 7.43/2.57  tff(c_7729, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_7649, c_7726])).
% 7.43/2.57  tff(c_7738, plain, ('#skF_6'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6941, c_7729])).
% 7.43/2.57  tff(c_7681, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7649, c_86])).
% 7.43/2.57  tff(c_7745, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7738, c_7738, c_7681])).
% 7.43/2.57  tff(c_6938, plain, (![B_6]: (k2_zfmisc_1('#skF_6', B_6)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6921, c_6921, c_18])).
% 7.43/2.57  tff(c_7749, plain, (![B_6]: (k2_zfmisc_1('#skF_3', B_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7738, c_7738, c_6938])).
% 7.43/2.57  tff(c_6985, plain, (![A_693]: (A_693='#skF_6' | ~v1_xboole_0(A_693))), inference(demodulation, [status(thm), theory('equality')], [c_6921, c_12])).
% 7.43/2.57  tff(c_6992, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_6913, c_6985])).
% 7.43/2.57  tff(c_6968, plain, (![B_6, A_5]: (B_6='#skF_6' | A_5='#skF_6' | k2_zfmisc_1(A_5, B_6)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6921, c_6921, c_6921, c_14])).
% 7.43/2.57  tff(c_7024, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_6992, c_6968])).
% 7.43/2.57  tff(c_7031, plain, ('#skF_6'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6941, c_7024])).
% 7.43/2.57  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.43/2.57  tff(c_6944, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6921, c_6921, c_40])).
% 7.43/2.57  tff(c_7040, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7031, c_7031, c_6944])).
% 7.43/2.57  tff(c_7019, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6992, c_86])).
% 7.43/2.57  tff(c_7077, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7031, c_7031, c_7019])).
% 7.43/2.57  tff(c_7035, plain, (![B_6]: (k2_zfmisc_1('#skF_3', B_6)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7031, c_7031, c_6938])).
% 7.43/2.57  tff(c_7458, plain, (![A_748, B_749, C_750]: (k1_relset_1(A_748, B_749, C_750)=k1_relat_1(C_750) | ~m1_subset_1(C_750, k1_zfmisc_1(k2_zfmisc_1(A_748, B_749))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.43/2.57  tff(c_7481, plain, (![B_754, C_755]: (k1_relset_1('#skF_3', B_754, C_755)=k1_relat_1(C_755) | ~m1_subset_1(C_755, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7035, c_7458])).
% 7.43/2.57  tff(c_7483, plain, (![B_754]: (k1_relset_1('#skF_3', B_754, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_7077, c_7481])).
% 7.43/2.57  tff(c_7485, plain, (![B_754]: (k1_relset_1('#skF_3', B_754, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7040, c_7483])).
% 7.43/2.57  tff(c_7044, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7031, c_6921])).
% 7.43/2.57  tff(c_66, plain, (![C_51, B_50]: (v1_funct_2(C_51, k1_xboole_0, B_50) | k1_relset_1(k1_xboole_0, B_50, C_51)!=k1_xboole_0 | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_50))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.43/2.57  tff(c_94, plain, (![C_51, B_50]: (v1_funct_2(C_51, k1_xboole_0, B_50) | k1_relset_1(k1_xboole_0, B_50, C_51)!=k1_xboole_0 | ~m1_subset_1(C_51, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_66])).
% 7.43/2.57  tff(c_7615, plain, (![C_765, B_766]: (v1_funct_2(C_765, '#skF_3', B_766) | k1_relset_1('#skF_3', B_766, C_765)!='#skF_3' | ~m1_subset_1(C_765, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_7044, c_7044, c_7044, c_7044, c_94])).
% 7.43/2.57  tff(c_7617, plain, (![B_766]: (v1_funct_2('#skF_3', '#skF_3', B_766) | k1_relset_1('#skF_3', B_766, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_7077, c_7615])).
% 7.43/2.57  tff(c_7620, plain, (![B_766]: (v1_funct_2('#skF_3', '#skF_3', B_766))), inference(demodulation, [status(thm), theory('equality')], [c_7485, c_7617])).
% 7.43/2.57  tff(c_6953, plain, (~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_92])).
% 7.43/2.57  tff(c_7039, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7031, c_6953])).
% 7.43/2.57  tff(c_7625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7620, c_7039])).
% 7.43/2.57  tff(c_7626, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_92])).
% 7.43/2.57  tff(c_7747, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_7738, c_7626])).
% 7.43/2.57  tff(c_7872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7745, c_7749, c_7747])).
% 7.43/2.57  tff(c_7874, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_82])).
% 7.43/2.57  tff(c_7873, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_82])).
% 7.43/2.57  tff(c_7884, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7874, c_7873])).
% 7.43/2.57  tff(c_7877, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7873, c_7873, c_40])).
% 7.43/2.57  tff(c_7899, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7884, c_7884, c_7877])).
% 7.43/2.57  tff(c_7879, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7873, c_2])).
% 7.43/2.57  tff(c_7895, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7884, c_7879])).
% 7.43/2.57  tff(c_7916, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7874, c_7874, c_16])).
% 7.43/2.57  tff(c_7889, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7884, c_86])).
% 7.43/2.57  tff(c_7926, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7916, c_7889])).
% 7.43/2.57  tff(c_8000, plain, (![B_800, A_801]: (v1_xboole_0(B_800) | ~m1_subset_1(B_800, k1_zfmisc_1(A_801)) | ~v1_xboole_0(A_801))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.43/2.57  tff(c_8003, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_7926, c_8000])).
% 7.43/2.57  tff(c_8006, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7895, c_8003])).
% 7.43/2.57  tff(c_7875, plain, (![A_4]: (A_4='#skF_3' | ~v1_xboole_0(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_7873, c_12])).
% 7.43/2.57  tff(c_7909, plain, (![A_4]: (A_4='#skF_4' | ~v1_xboole_0(A_4))), inference(demodulation, [status(thm), theory('equality')], [c_7884, c_7875])).
% 7.43/2.57  tff(c_8014, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_8006, c_7909])).
% 7.43/2.57  tff(c_8024, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8014, c_7926])).
% 7.43/2.57  tff(c_7933, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7874, c_7874, c_18])).
% 7.43/2.57  tff(c_8292, plain, (![A_844, B_845, C_846]: (k1_relset_1(A_844, B_845, C_846)=k1_relat_1(C_846) | ~m1_subset_1(C_846, k1_zfmisc_1(k2_zfmisc_1(A_844, B_845))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.43/2.57  tff(c_8299, plain, (![B_847, C_848]: (k1_relset_1('#skF_4', B_847, C_848)=k1_relat_1(C_848) | ~m1_subset_1(C_848, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_7933, c_8292])).
% 7.43/2.57  tff(c_8301, plain, (![B_847]: (k1_relset_1('#skF_4', B_847, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8024, c_8299])).
% 7.43/2.57  tff(c_8303, plain, (![B_847]: (k1_relset_1('#skF_4', B_847, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7899, c_8301])).
% 7.43/2.57  tff(c_8512, plain, (![C_865, B_866]: (v1_funct_2(C_865, '#skF_4', B_866) | k1_relset_1('#skF_4', B_866, C_865)!='#skF_4' | ~m1_subset_1(C_865, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7874, c_7874, c_7874, c_7874, c_94])).
% 7.43/2.57  tff(c_8514, plain, (![B_866]: (v1_funct_2('#skF_4', '#skF_4', B_866) | k1_relset_1('#skF_4', B_866, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_8024, c_8512])).
% 7.43/2.57  tff(c_8517, plain, (![B_866]: (v1_funct_2('#skF_4', '#skF_4', B_866))), inference(demodulation, [status(thm), theory('equality')], [c_8303, c_8514])).
% 7.43/2.57  tff(c_8016, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7884, c_7926, c_7933, c_7884, c_92])).
% 7.43/2.57  tff(c_8022, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8014, c_8016])).
% 7.43/2.57  tff(c_8521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8517, c_8022])).
% 7.43/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/2.57  
% 7.43/2.57  Inference rules
% 7.43/2.57  ----------------------
% 7.43/2.57  #Ref     : 0
% 7.43/2.57  #Sup     : 1643
% 7.43/2.57  #Fact    : 0
% 7.43/2.57  #Define  : 0
% 7.43/2.57  #Split   : 30
% 7.43/2.57  #Chain   : 0
% 7.43/2.57  #Close   : 0
% 7.43/2.57  
% 7.43/2.57  Ordering : KBO
% 7.43/2.57  
% 7.43/2.57  Simplification rules
% 7.43/2.57  ----------------------
% 7.43/2.57  #Subsume      : 392
% 7.43/2.57  #Demod        : 2521
% 7.43/2.57  #Tautology    : 786
% 7.43/2.57  #SimpNegUnit  : 53
% 7.43/2.57  #BackRed      : 299
% 7.43/2.57  
% 7.43/2.57  #Partial instantiations: 0
% 7.43/2.57  #Strategies tried      : 1
% 7.43/2.57  
% 7.43/2.57  Timing (in seconds)
% 7.43/2.57  ----------------------
% 7.43/2.57  Preprocessing        : 0.41
% 7.43/2.57  Parsing              : 0.20
% 7.43/2.57  CNF conversion       : 0.03
% 7.43/2.57  Main loop            : 1.29
% 7.43/2.57  Inferencing          : 0.44
% 7.43/2.57  Reduction            : 0.45
% 7.43/2.57  Demodulation         : 0.32
% 7.43/2.57  BG Simplification    : 0.05
% 7.43/2.57  Subsumption          : 0.25
% 7.43/2.57  Abstraction          : 0.05
% 7.43/2.57  MUC search           : 0.00
% 7.43/2.57  Cooper               : 0.00
% 7.43/2.57  Total                : 1.77
% 7.43/2.57  Index Insertion      : 0.00
% 7.43/2.58  Index Deletion       : 0.00
% 7.43/2.58  Index Matching       : 0.00
% 7.43/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
