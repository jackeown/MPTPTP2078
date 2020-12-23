%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:09 EST 2020

% Result     : Theorem 25.94s
% Output     : CNFRefutation 27.04s
% Verified   : 
% Statistics : Number of formulae       : 1191 (21813 expanded)
%              Number of leaves         :   48 (7202 expanded)
%              Depth                    :   20
%              Number of atoms          : 1906 (41331 expanded)
%              Number of equality atoms :  803 (8374 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(f_82,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_113,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_89,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_159,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(c_32,plain,(
    ! [A_27,B_28] : r1_xboole_0(k4_xboole_0(A_27,B_28),B_28) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_88,plain,(
    ! [B_74,A_75] :
      ( r1_xboole_0(B_74,A_75)
      | ~ r1_xboole_0(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k4_xboole_0(A_27,B_28)) ),
    inference(resolution,[status(thm)],[c_32,c_88])).

tff(c_97,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = A_78
      | ~ r1_xboole_0(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_104,plain,(
    ! [B_28,A_27] : k4_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = B_28 ),
    inference(resolution,[status(thm)],[c_91,c_97])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89092,plain,(
    ! [A_4744,B_4745,C_4746] :
      ( ~ r1_xboole_0(A_4744,B_4745)
      | ~ r2_hidden(C_4746,k3_xboole_0(A_4744,B_4745)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_89102,plain,(
    ! [A_4744,B_4745] :
      ( ~ r1_xboole_0(A_4744,B_4745)
      | v1_xboole_0(k3_xboole_0(A_4744,B_4745)) ) ),
    inference(resolution,[status(thm)],[c_4,c_89092])).

tff(c_89080,plain,(
    ! [A_4740,B_4741] :
      ( r2_hidden('#skF_2'(A_4740,B_4741),A_4740)
      | r1_tarski(A_4740,B_4741) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89090,plain,(
    ! [A_4740,B_4741] :
      ( ~ v1_xboole_0(A_4740)
      | r1_tarski(A_4740,B_4741) ) ),
    inference(resolution,[status(thm)],[c_89080,c_2])).

tff(c_24,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_89105,plain,(
    ! [B_4749,A_4750] :
      ( B_4749 = A_4750
      | ~ r1_tarski(B_4749,A_4750)
      | ~ r1_tarski(A_4750,B_4749) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_89130,plain,(
    ! [A_4751] :
      ( k1_xboole_0 = A_4751
      | ~ r1_tarski(A_4751,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_89105])).

tff(c_89153,plain,(
    ! [A_4752] :
      ( k1_xboole_0 = A_4752
      | ~ v1_xboole_0(A_4752) ) ),
    inference(resolution,[status(thm)],[c_89090,c_89130])).

tff(c_140143,plain,(
    ! [A_7641,B_7642] :
      ( k3_xboole_0(A_7641,B_7642) = k1_xboole_0
      | ~ r1_xboole_0(A_7641,B_7642) ) ),
    inference(resolution,[status(thm)],[c_89102,c_89153])).

tff(c_140168,plain,(
    ! [B_7643,A_7644] : k3_xboole_0(B_7643,k4_xboole_0(A_7644,B_7643)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_140143])).

tff(c_139946,plain,(
    ! [A_7620,B_7621] : k4_xboole_0(A_7620,k4_xboole_0(A_7620,B_7621)) = k3_xboole_0(A_7620,B_7621) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_139962,plain,(
    ! [A_7620,B_7621] : r1_xboole_0(k4_xboole_0(A_7620,B_7621),k3_xboole_0(A_7620,B_7621)) ),
    inference(superposition,[status(thm),theory(equality)],[c_139946,c_91])).

tff(c_140173,plain,(
    ! [B_7643,A_7644] : r1_xboole_0(k4_xboole_0(B_7643,k4_xboole_0(A_7644,B_7643)),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_140168,c_139962])).

tff(c_140212,plain,(
    ! [B_7648] : r1_xboole_0(B_7648,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_140173])).

tff(c_89157,plain,(
    ! [A_4744,B_4745] :
      ( k3_xboole_0(A_4744,B_4745) = k1_xboole_0
      | ~ r1_xboole_0(A_4744,B_4745) ) ),
    inference(resolution,[status(thm)],[c_89102,c_89153])).

tff(c_140231,plain,(
    ! [B_7648] : k3_xboole_0(B_7648,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_140212,c_89157])).

tff(c_34,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = A_29
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_140355,plain,(
    ! [B_7653] : k4_xboole_0(B_7653,k1_xboole_0) = B_7653 ),
    inference(resolution,[status(thm)],[c_140212,c_34])).

tff(c_26,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_140380,plain,(
    ! [B_7653] : k4_xboole_0(B_7653,B_7653) = k3_xboole_0(B_7653,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_140355,c_26])).

tff(c_140747,plain,(
    ! [B_7653] : k4_xboole_0(B_7653,B_7653) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140231,c_140380])).

tff(c_89053,plain,(
    ! [A_4730,B_4731] :
      ( r1_xboole_0(A_4730,B_4731)
      | k4_xboole_0(A_4730,B_4731) != A_4730 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_xboole_0(B_11,A_10)
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_89060,plain,(
    ! [B_4731,A_4730] :
      ( r1_xboole_0(B_4731,A_4730)
      | k4_xboole_0(A_4730,B_4731) != A_4730 ) ),
    inference(resolution,[status(thm)],[c_89053,c_12])).

tff(c_139986,plain,(
    ! [B_7622] : k3_xboole_0(B_7622,B_7622) = B_7622 ),
    inference(superposition,[status(thm),theory(equality)],[c_139946,c_104])).

tff(c_140007,plain,(
    ! [B_7623] :
      ( ~ r1_xboole_0(B_7623,B_7623)
      | v1_xboole_0(B_7623) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139986,c_89102])).

tff(c_140016,plain,(
    ! [A_4730] :
      ( v1_xboole_0(A_4730)
      | k4_xboole_0(A_4730,A_4730) != A_4730 ) ),
    inference(resolution,[status(thm)],[c_89060,c_140007])).

tff(c_140748,plain,(
    ! [A_4730] :
      ( v1_xboole_0(A_4730)
      | k1_xboole_0 != A_4730 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140747,c_140016])).

tff(c_50,plain,(
    ! [A_44,B_45,C_46] : k2_zfmisc_1(k2_zfmisc_1(A_44,B_45),C_46) = k3_zfmisc_1(A_44,B_45,C_46) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_tarski(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k1_tarski(A_32),k1_zfmisc_1(B_33))
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_141516,plain,(
    ! [C_7722,B_7723,A_7724] :
      ( v1_xboole_0(C_7722)
      | ~ m1_subset_1(C_7722,k1_zfmisc_1(k2_zfmisc_1(B_7723,A_7724)))
      | ~ v1_xboole_0(A_7724) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_141523,plain,(
    ! [A_32,A_7724,B_7723] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_7724)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_7723,A_7724)) ) ),
    inference(resolution,[status(thm)],[c_40,c_141516])).

tff(c_141684,plain,(
    ! [A_7731,A_7732,B_7733] :
      ( ~ v1_xboole_0(A_7731)
      | ~ r2_hidden(A_7732,k2_zfmisc_1(B_7733,A_7731)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_141523])).

tff(c_141703,plain,(
    ! [A_7734,B_7735] :
      ( ~ v1_xboole_0(A_7734)
      | v1_xboole_0(k2_zfmisc_1(B_7735,A_7734)) ) ),
    inference(resolution,[status(thm)],[c_4,c_141684])).

tff(c_144939,plain,(
    ! [C_7919,A_7920,B_7921] :
      ( ~ v1_xboole_0(C_7919)
      | v1_xboole_0(k3_zfmisc_1(A_7920,B_7921,C_7919)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_141703])).

tff(c_123768,plain,(
    ! [A_6727,B_6728] :
      ( k3_xboole_0(A_6727,B_6728) = k1_xboole_0
      | ~ r1_xboole_0(A_6727,B_6728) ) ),
    inference(resolution,[status(thm)],[c_89102,c_89153])).

tff(c_123795,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_123768])).

tff(c_123583,plain,(
    ! [A_6708,B_6709] : k4_xboole_0(A_6708,k4_xboole_0(A_6708,B_6709)) = k3_xboole_0(A_6708,B_6709) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123678,plain,(
    ! [A_6717,B_6718] : r1_xboole_0(k4_xboole_0(A_6717,B_6718),k3_xboole_0(A_6717,B_6718)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123583,c_91])).

tff(c_123692,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_123678])).

tff(c_123829,plain,(
    ! [B_6731] : r1_xboole_0(B_6731,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123795,c_123692])).

tff(c_123848,plain,(
    ! [B_6731] : k3_xboole_0(B_6731,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123829,c_89157])).

tff(c_123960,plain,(
    ! [B_6741] : k4_xboole_0(B_6741,k1_xboole_0) = B_6741 ),
    inference(resolution,[status(thm)],[c_123829,c_34])).

tff(c_123981,plain,(
    ! [B_6741] : k4_xboole_0(B_6741,B_6741) = k3_xboole_0(B_6741,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_123960,c_26])).

tff(c_124001,plain,(
    ! [B_6741] : k4_xboole_0(B_6741,B_6741) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_123848,c_123981])).

tff(c_36,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(A_29,B_30)
      | k4_xboole_0(A_29,B_30) != A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_123618,plain,(
    ! [B_6710] : k3_xboole_0(B_6710,B_6710) = B_6710 ),
    inference(superposition,[status(thm),theory(equality)],[c_123583,c_104])).

tff(c_123634,plain,(
    ! [B_6711] :
      ( ~ r1_xboole_0(B_6711,B_6711)
      | v1_xboole_0(B_6711) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123618,c_89102])).

tff(c_123644,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k4_xboole_0(B_30,B_30) != B_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_123634])).

tff(c_124219,plain,(
    ! [B_6749] :
      ( v1_xboole_0(B_6749)
      | k1_xboole_0 != B_6749 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124001,c_123644])).

tff(c_72,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_106,plain,(
    ! [A_80,B_81] :
      ( r1_tarski(A_80,B_81)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_118,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_106])).

tff(c_89122,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_118,c_89105])).

tff(c_117075,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_89122])).

tff(c_117079,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_89090,c_117075])).

tff(c_124238,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_124219,c_117079])).

tff(c_124144,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k1_xboole_0 != B_30 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124001,c_123644])).

tff(c_124475,plain,(
    ! [C_6772,B_6773,A_6774] :
      ( v1_xboole_0(C_6772)
      | ~ m1_subset_1(C_6772,k1_zfmisc_1(k2_zfmisc_1(B_6773,A_6774)))
      | ~ v1_xboole_0(A_6774) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_124482,plain,(
    ! [A_32,A_6774,B_6773] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_6774)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_6773,A_6774)) ) ),
    inference(resolution,[status(thm)],[c_40,c_124475])).

tff(c_124491,plain,(
    ! [A_6775,A_6776,B_6777] :
      ( ~ v1_xboole_0(A_6775)
      | ~ r2_hidden(A_6776,k2_zfmisc_1(B_6777,A_6775)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_124482])).

tff(c_124505,plain,(
    ! [A_6778,B_6779] :
      ( ~ v1_xboole_0(A_6778)
      | v1_xboole_0(k2_zfmisc_1(B_6779,A_6778)) ) ),
    inference(resolution,[status(thm)],[c_4,c_124491])).

tff(c_124673,plain,(
    ! [C_6790,A_6791,B_6792] :
      ( ~ v1_xboole_0(C_6790)
      | v1_xboole_0(k3_zfmisc_1(A_6791,B_6792,C_6790)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_124505])).

tff(c_64,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_82,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_64,c_2])).

tff(c_124690,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_124673,c_82])).

tff(c_124713,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(resolution,[status(thm)],[c_124144,c_124690])).

tff(c_117372,plain,(
    ! [A_6344,B_6345] :
      ( k3_xboole_0(A_6344,B_6345) = k1_xboole_0
      | ~ r1_xboole_0(A_6344,B_6345) ) ),
    inference(resolution,[status(thm)],[c_89102,c_89153])).

tff(c_117403,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_117372])).

tff(c_117085,plain,(
    ! [A_6312,B_6313] : k4_xboole_0(A_6312,k4_xboole_0(A_6312,B_6313)) = k3_xboole_0(A_6312,B_6313) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_117244,plain,(
    ! [A_6328,B_6329] : r1_xboole_0(k4_xboole_0(A_6328,B_6329),k3_xboole_0(A_6328,B_6329)) ),
    inference(superposition,[status(thm),theory(equality)],[c_117085,c_91])).

tff(c_117261,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_117244])).

tff(c_117438,plain,(
    ! [B_6348] : r1_xboole_0(B_6348,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117403,c_117261])).

tff(c_117459,plain,(
    ! [B_6348] : k3_xboole_0(B_6348,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117438,c_89157])).

tff(c_117600,plain,(
    ! [B_6358] : k4_xboole_0(B_6358,k1_xboole_0) = B_6358 ),
    inference(resolution,[status(thm)],[c_117438,c_34])).

tff(c_117625,plain,(
    ! [B_6358] : k4_xboole_0(B_6358,B_6358) = k3_xboole_0(B_6358,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_117600,c_26])).

tff(c_117961,plain,(
    ! [B_6358] : k4_xboole_0(B_6358,B_6358) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117459,c_117625])).

tff(c_117120,plain,(
    ! [A_6314] : k3_xboole_0(A_6314,A_6314) = A_6314 ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_117085])).

tff(c_117140,plain,(
    ! [A_6315] :
      ( ~ r1_xboole_0(A_6315,A_6315)
      | v1_xboole_0(A_6315) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117120,c_89102])).

tff(c_117149,plain,(
    ! [A_4730] :
      ( v1_xboole_0(A_4730)
      | k4_xboole_0(A_4730,A_4730) != A_4730 ) ),
    inference(resolution,[status(thm)],[c_89060,c_117140])).

tff(c_118028,plain,(
    ! [A_6379] :
      ( v1_xboole_0(A_6379)
      | k1_xboole_0 != A_6379 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117961,c_117149])).

tff(c_118051,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_118028,c_117079])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_117,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_106])).

tff(c_89123,plain,
    ( '#skF_5' = '#skF_8'
    | ~ r1_tarski('#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_117,c_89105])).

tff(c_117080,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_89123])).

tff(c_117084,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_89090,c_117080])).

tff(c_118050,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_118028,c_117084])).

tff(c_107896,plain,(
    ! [A_5827,B_5828] :
      ( k3_xboole_0(A_5827,B_5828) = k1_xboole_0
      | ~ r1_xboole_0(A_5827,B_5828) ) ),
    inference(resolution,[status(thm)],[c_89102,c_89153])).

tff(c_107927,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_107896])).

tff(c_89159,plain,(
    ! [A_4753,B_4754] : k4_xboole_0(A_4753,k4_xboole_0(A_4753,B_4754)) = k3_xboole_0(A_4753,B_4754) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_107733,plain,(
    ! [A_5807,B_5808] : r1_xboole_0(k3_xboole_0(A_5807,B_5808),k4_xboole_0(A_5807,B_5808)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89159,c_32])).

tff(c_107781,plain,(
    ! [A_5813,B_5814] : r1_xboole_0(k4_xboole_0(A_5813,B_5814),k3_xboole_0(A_5813,B_5814)) ),
    inference(resolution,[status(thm)],[c_107733,c_12])).

tff(c_107798,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_107781])).

tff(c_107981,plain,(
    ! [B_5834] : r1_xboole_0(B_5834,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107927,c_107798])).

tff(c_108004,plain,(
    ! [B_5834] : k3_xboole_0(B_5834,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_107981,c_89157])).

tff(c_108208,plain,(
    ! [B_5844] : k4_xboole_0(B_5844,k1_xboole_0) = B_5844 ),
    inference(resolution,[status(thm)],[c_107981,c_34])).

tff(c_108233,plain,(
    ! [B_5844] : k4_xboole_0(B_5844,B_5844) = k3_xboole_0(B_5844,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108208,c_26])).

tff(c_108258,plain,(
    ! [B_5844] : k4_xboole_0(B_5844,B_5844) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108004,c_108233])).

tff(c_89198,plain,(
    ! [A_4755] : k3_xboole_0(A_4755,A_4755) = A_4755 ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_89159])).

tff(c_107668,plain,(
    ! [A_5800] :
      ( ~ r1_xboole_0(A_5800,A_5800)
      | v1_xboole_0(A_5800) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89198,c_89102])).

tff(c_107678,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k4_xboole_0(B_30,B_30) != B_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_107668])).

tff(c_108418,plain,(
    ! [B_5852] :
      ( v1_xboole_0(B_5852)
      | k1_xboole_0 != B_5852 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108258,c_107678])).

tff(c_93821,plain,(
    ! [A_5057,B_5058] :
      ( k3_xboole_0(A_5057,B_5058) = k1_xboole_0
      | ~ r1_xboole_0(A_5057,B_5058) ) ),
    inference(resolution,[status(thm)],[c_89102,c_89153])).

tff(c_93852,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_93821])).

tff(c_93702,plain,(
    ! [A_5043,B_5044] : r1_xboole_0(k4_xboole_0(A_5043,B_5044),k3_xboole_0(A_5043,B_5044)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89159,c_91])).

tff(c_93719,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_93702])).

tff(c_93887,plain,(
    ! [B_5061] : r1_xboole_0(B_5061,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93852,c_93719])).

tff(c_93906,plain,(
    ! [B_5061] : k3_xboole_0(B_5061,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93887,c_89157])).

tff(c_94174,plain,(
    ! [B_5074] : k4_xboole_0(B_5074,k1_xboole_0) = B_5074 ),
    inference(resolution,[status(thm)],[c_93887,c_34])).

tff(c_94199,plain,(
    ! [B_5074] : k4_xboole_0(B_5074,B_5074) = k3_xboole_0(B_5074,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_94174,c_26])).

tff(c_94225,plain,(
    ! [B_5074] : k4_xboole_0(B_5074,B_5074) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93906,c_94199])).

tff(c_93594,plain,(
    ! [A_5030] :
      ( ~ r1_xboole_0(A_5030,A_5030)
      | v1_xboole_0(A_5030) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89198,c_89102])).

tff(c_93604,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k4_xboole_0(B_30,B_30) != B_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_93594])).

tff(c_94310,plain,(
    ! [B_5077] :
      ( v1_xboole_0(B_5077)
      | k1_xboole_0 != B_5077 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94225,c_93604])).

tff(c_89213,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_89122])).

tff(c_89217,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_89090,c_89213])).

tff(c_94332,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_94310,c_89217])).

tff(c_68,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_116,plain,(
    r1_tarski('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_106])).

tff(c_89124,plain,
    ( '#skF_6' = '#skF_9'
    | ~ r1_tarski('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_116,c_89105])).

tff(c_89158,plain,(
    ~ r1_tarski('#skF_6','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_89124])).

tff(c_89197,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_89090,c_89158])).

tff(c_94333,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_94310,c_89197])).

tff(c_89476,plain,(
    ! [A_4791,B_4792] :
      ( k3_xboole_0(A_4791,B_4792) = k1_xboole_0
      | ~ r1_xboole_0(A_4791,B_4792) ) ),
    inference(resolution,[status(thm)],[c_89102,c_89153])).

tff(c_89507,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_89476])).

tff(c_89328,plain,(
    ! [A_4771,B_4772] : r1_xboole_0(k4_xboole_0(A_4771,B_4772),k3_xboole_0(A_4771,B_4772)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89159,c_91])).

tff(c_89345,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_89328])).

tff(c_89582,plain,(
    ! [B_4797] : r1_xboole_0(B_4797,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89507,c_89345])).

tff(c_89601,plain,(
    ! [B_4797] : k3_xboole_0(B_4797,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_89582,c_89157])).

tff(c_89783,plain,(
    ! [B_4805] : k4_xboole_0(B_4805,k1_xboole_0) = B_4805 ),
    inference(resolution,[status(thm)],[c_89582,c_34])).

tff(c_89808,plain,(
    ! [B_4805] : k4_xboole_0(B_4805,B_4805) = k3_xboole_0(B_4805,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_89783,c_26])).

tff(c_89833,plain,(
    ! [B_4805] : k4_xboole_0(B_4805,B_4805) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89601,c_89808])).

tff(c_89241,plain,(
    ! [A_4758] :
      ( ~ r1_xboole_0(A_4758,A_4758)
      | v1_xboole_0(A_4758) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89198,c_89102])).

tff(c_89251,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k4_xboole_0(B_30,B_30) != B_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_89241])).

tff(c_89986,plain,(
    ! [B_4812] :
      ( v1_xboole_0(B_4812)
      | k1_xboole_0 != B_4812 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89833,c_89251])).

tff(c_90012,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_89986,c_89217])).

tff(c_89219,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_89123])).

tff(c_89223,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_89090,c_89219])).

tff(c_90011,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_89986,c_89223])).

tff(c_90013,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_89986,c_89197])).

tff(c_66,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_90308,plain,(
    ! [A_4832,B_4833,C_4834,D_4835] :
      ( k7_mcart_1(A_4832,B_4833,C_4834,D_4835) = k2_mcart_1(D_4835)
      | ~ m1_subset_1(D_4835,k3_zfmisc_1(A_4832,B_4833,C_4834))
      | k1_xboole_0 = C_4834
      | k1_xboole_0 = B_4833
      | k1_xboole_0 = A_4832 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_90311,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_90308])).

tff(c_90314,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_90012,c_90011,c_90013,c_90311])).

tff(c_62,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9')
    | ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8')
    | ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_119,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_199,plain,(
    ! [A_93,B_94,C_95] :
      ( ~ r1_xboole_0(A_93,B_94)
      | ~ r2_hidden(C_95,k3_xboole_0(A_93,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_204,plain,(
    ! [A_93,B_94] :
      ( ~ r1_xboole_0(A_93,B_94)
      | v1_xboole_0(k3_xboole_0(A_93,B_94)) ) ),
    inference(resolution,[status(thm)],[c_4,c_199])).

tff(c_268,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_2'(A_102,B_103),A_102)
      | r1_tarski(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_278,plain,(
    ! [A_104,B_105] :
      ( ~ v1_xboole_0(A_104)
      | r1_tarski(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_268,c_2])).

tff(c_164,plain,(
    ! [B_90,A_91] :
      ( B_90 = A_91
      | ~ r1_tarski(B_90,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_182,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_164])).

tff(c_299,plain,(
    ! [A_106] :
      ( k1_xboole_0 = A_106
      | ~ v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_278,c_182])).

tff(c_489,plain,(
    ! [A_134,B_135] :
      ( k3_xboole_0(A_134,B_135) = k1_xboole_0
      | ~ r1_xboole_0(A_134,B_135) ) ),
    inference(resolution,[status(thm)],[c_204,c_299])).

tff(c_514,plain,(
    ! [B_136,A_137] : k3_xboole_0(B_136,k4_xboole_0(A_137,B_136)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_489])).

tff(c_206,plain,(
    ! [A_98,B_99] : k4_xboole_0(A_98,k4_xboole_0(A_98,B_99)) = k3_xboole_0(A_98,B_99) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_336,plain,(
    ! [A_114,B_115] : r1_xboole_0(k3_xboole_0(A_114,B_115),k4_xboole_0(A_114,B_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_32])).

tff(c_356,plain,(
    ! [A_114,B_115] : r1_xboole_0(k4_xboole_0(A_114,B_115),k3_xboole_0(A_114,B_115)) ),
    inference(resolution,[status(thm)],[c_336,c_12])).

tff(c_519,plain,(
    ! [B_136,A_137] : r1_xboole_0(k4_xboole_0(B_136,k4_xboole_0(A_137,B_136)),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_356])).

tff(c_554,plain,(
    ! [B_141] : r1_xboole_0(B_141,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_519])).

tff(c_303,plain,(
    ! [A_93,B_94] :
      ( k3_xboole_0(A_93,B_94) = k1_xboole_0
      | ~ r1_xboole_0(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_204,c_299])).

tff(c_573,plain,(
    ! [B_141] : k3_xboole_0(B_141,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_554,c_303])).

tff(c_697,plain,(
    ! [B_146] : k4_xboole_0(B_146,k1_xboole_0) = B_146 ),
    inference(resolution,[status(thm)],[c_554,c_34])).

tff(c_722,plain,(
    ! [B_146] : k4_xboole_0(B_146,B_146) = k3_xboole_0(B_146,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_26])).

tff(c_1015,plain,(
    ! [B_146] : k4_xboole_0(B_146,B_146) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_722])).

tff(c_148,plain,(
    ! [A_86,B_87] :
      ( r1_xboole_0(A_86,B_87)
      | k4_xboole_0(A_86,B_87) != A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_155,plain,(
    ! [B_87,A_86] :
      ( r1_xboole_0(B_87,A_86)
      | k4_xboole_0(A_86,B_87) != A_86 ) ),
    inference(resolution,[status(thm)],[c_148,c_12])).

tff(c_241,plain,(
    ! [B_100] : k3_xboole_0(B_100,B_100) = B_100 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_104])).

tff(c_257,plain,(
    ! [B_101] :
      ( ~ r1_xboole_0(B_101,B_101)
      | v1_xboole_0(B_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_204])).

tff(c_266,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | k4_xboole_0(A_86,A_86) != A_86 ) ),
    inference(resolution,[status(thm)],[c_155,c_257])).

tff(c_1082,plain,(
    ! [A_167] :
      ( v1_xboole_0(A_167)
      | k1_xboole_0 != A_167 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_266])).

tff(c_175,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_118,c_164])).

tff(c_197,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_295,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_278,c_197])).

tff(c_1106,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_1082,c_295])).

tff(c_176,plain,
    ( '#skF_5' = '#skF_8'
    | ~ r1_tarski('#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_117,c_164])).

tff(c_196,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_296,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_278,c_196])).

tff(c_1105,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_1082,c_296])).

tff(c_177,plain,
    ( '#skF_6' = '#skF_9'
    | ~ r1_tarski('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_116,c_164])).

tff(c_198,plain,(
    ~ r1_tarski('#skF_6','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_294,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_278,c_198])).

tff(c_1107,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_1082,c_294])).

tff(c_1344,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( k5_mcart_1(A_200,B_201,C_202,D_203) = k1_mcart_1(k1_mcart_1(D_203))
      | ~ m1_subset_1(D_203,k3_zfmisc_1(A_200,B_201,C_202))
      | k1_xboole_0 = C_202
      | k1_xboole_0 = B_201
      | k1_xboole_0 = A_200 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1347,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_1344])).

tff(c_1350,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_1106,c_1105,c_1107,c_1347])).

tff(c_901,plain,(
    ! [A_156,B_157,C_158] : k2_zfmisc_1(k2_zfmisc_1(A_156,B_157),C_158) = k3_zfmisc_1(A_156,B_157,C_158) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_54,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden(k1_mcart_1(A_47),B_48)
      | ~ r2_hidden(A_47,k2_zfmisc_1(B_48,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_5919,plain,(
    ! [A_417,A_418,B_419,C_420] :
      ( r2_hidden(k1_mcart_1(A_417),k2_zfmisc_1(A_418,B_419))
      | ~ r2_hidden(A_417,k3_zfmisc_1(A_418,B_419,C_420)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_901,c_54])).

tff(c_5956,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_5919])).

tff(c_5972,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_5956,c_54])).

tff(c_5991,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1350,c_5972])).

tff(c_5993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_5991])).

tff(c_5994,plain,(
    '#skF_6' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_5996,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5994,c_119])).

tff(c_6189,plain,(
    ! [A_446,B_447,C_448] :
      ( ~ r1_xboole_0(A_446,B_447)
      | ~ r2_hidden(C_448,k3_xboole_0(A_446,B_447)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6235,plain,(
    ! [A_453,B_454] :
      ( ~ r1_xboole_0(A_453,B_454)
      | v1_xboole_0(k3_xboole_0(A_453,B_454)) ) ),
    inference(resolution,[status(thm)],[c_4,c_6189])).

tff(c_6037,plain,(
    ! [A_425,B_426] :
      ( r2_hidden('#skF_2'(A_425,B_426),A_425)
      | r1_tarski(A_425,B_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6042,plain,(
    ! [A_427,B_428] :
      ( ~ v1_xboole_0(A_427)
      | r1_tarski(A_427,B_428) ) ),
    inference(resolution,[status(thm)],[c_6037,c_2])).

tff(c_6062,plain,(
    ! [A_427] :
      ( k1_xboole_0 = A_427
      | ~ v1_xboole_0(A_427) ) ),
    inference(resolution,[status(thm)],[c_6042,c_182])).

tff(c_6331,plain,(
    ! [A_467,B_468] :
      ( k3_xboole_0(A_467,B_468) = k1_xboole_0
      | ~ r1_xboole_0(A_467,B_468) ) ),
    inference(resolution,[status(thm)],[c_6235,c_6062])).

tff(c_6358,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_6331])).

tff(c_6142,plain,(
    ! [A_443,B_444] : k4_xboole_0(A_443,k4_xboole_0(A_443,B_444)) = k3_xboole_0(A_443,B_444) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6213,plain,(
    ! [A_451,B_452] : r1_xboole_0(k3_xboole_0(A_451,B_452),k4_xboole_0(A_451,B_452)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6142,c_32])).

tff(c_6274,plain,(
    ! [A_460,B_461] : r1_xboole_0(k4_xboole_0(A_460,B_461),k3_xboole_0(A_460,B_461)) ),
    inference(resolution,[status(thm)],[c_6213,c_12])).

tff(c_6293,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_6274])).

tff(c_6392,plain,(
    ! [B_471] : r1_xboole_0(B_471,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6358,c_6293])).

tff(c_6245,plain,(
    ! [A_453,B_454] :
      ( k3_xboole_0(A_453,B_454) = k1_xboole_0
      | ~ r1_xboole_0(A_453,B_454) ) ),
    inference(resolution,[status(thm)],[c_6235,c_6062])).

tff(c_6413,plain,(
    ! [B_471] : k3_xboole_0(B_471,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6392,c_6245])).

tff(c_6497,plain,(
    ! [B_480] : k4_xboole_0(B_480,k1_xboole_0) = B_480 ),
    inference(resolution,[status(thm)],[c_6392,c_34])).

tff(c_6515,plain,(
    ! [B_480] : k4_xboole_0(B_480,B_480) = k3_xboole_0(B_480,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6497,c_26])).

tff(c_6816,plain,(
    ! [B_480] : k4_xboole_0(B_480,B_480) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6413,c_6515])).

tff(c_6158,plain,(
    ! [B_444] : k3_xboole_0(B_444,B_444) = B_444 ),
    inference(superposition,[status(thm),theory(equality)],[c_6142,c_104])).

tff(c_6246,plain,(
    ! [B_455] :
      ( ~ r1_xboole_0(B_455,B_455)
      | v1_xboole_0(B_455) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6158,c_6235])).

tff(c_6255,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | k4_xboole_0(A_86,A_86) != A_86 ) ),
    inference(resolution,[status(thm)],[c_155,c_6246])).

tff(c_6817,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | k1_xboole_0 != A_86 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6816,c_6255])).

tff(c_6799,plain,(
    ! [C_491,B_492,A_493] :
      ( v1_xboole_0(C_491)
      | ~ m1_subset_1(C_491,k1_zfmisc_1(k2_zfmisc_1(B_492,A_493)))
      | ~ v1_xboole_0(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6806,plain,(
    ! [A_32,A_493,B_492] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_493)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_492,A_493)) ) ),
    inference(resolution,[status(thm)],[c_40,c_6799])).

tff(c_7052,plain,(
    ! [A_511,A_512,B_513] :
      ( ~ v1_xboole_0(A_511)
      | ~ r2_hidden(A_512,k2_zfmisc_1(B_513,A_511)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_6806])).

tff(c_7066,plain,(
    ! [A_514,B_515] :
      ( ~ v1_xboole_0(A_514)
      | v1_xboole_0(k2_zfmisc_1(B_515,A_514)) ) ),
    inference(resolution,[status(thm)],[c_4,c_7052])).

tff(c_7402,plain,(
    ! [C_549,A_550,B_551] :
      ( ~ v1_xboole_0(C_549)
      | v1_xboole_0(k3_zfmisc_1(A_550,B_551,C_549)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_7066])).

tff(c_7422,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_7402,c_82])).

tff(c_7426,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(resolution,[status(thm)],[c_6817,c_7422])).

tff(c_6883,plain,(
    ! [A_495] :
      ( v1_xboole_0(A_495)
      | k1_xboole_0 != A_495 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6816,c_6255])).

tff(c_6060,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6042,c_197])).

tff(c_6904,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_6883,c_6060])).

tff(c_6061,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6042,c_196])).

tff(c_6903,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_6883,c_6061])).

tff(c_5998,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_5','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5994,c_66])).

tff(c_7394,plain,(
    ! [A_545,B_546,C_547,D_548] :
      ( k5_mcart_1(A_545,B_546,C_547,D_548) = k1_mcart_1(k1_mcart_1(D_548))
      | ~ m1_subset_1(D_548,k3_zfmisc_1(A_545,B_546,C_547))
      | k1_xboole_0 = C_547
      | k1_xboole_0 = B_546
      | k1_xboole_0 = A_545 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_7397,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5998,c_7394])).

tff(c_7400,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_6904,c_6903,c_7397])).

tff(c_8581,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_7426,c_7400])).

tff(c_6453,plain,(
    ! [A_476,B_477,C_478] :
      ( r2_hidden(k1_mcart_1(A_476),B_477)
      | ~ r2_hidden(A_476,k2_zfmisc_1(B_477,C_478)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_12866,plain,(
    ! [A_788,A_789,B_790,C_791] :
      ( r2_hidden(k1_mcart_1(A_788),k2_zfmisc_1(A_789,B_790))
      | ~ r2_hidden(A_788,k3_zfmisc_1(A_789,B_790,C_791)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_6453])).

tff(c_12906,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_12866])).

tff(c_12922,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_12906,c_54])).

tff(c_12940,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8581,c_12922])).

tff(c_12942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5996,c_12940])).

tff(c_12943,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_12945,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12943,c_119])).

tff(c_13090,plain,(
    ! [A_810,B_811,C_812] :
      ( ~ r1_xboole_0(A_810,B_811)
      | ~ r2_hidden(C_812,k3_xboole_0(A_810,B_811)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_13102,plain,(
    ! [A_815,B_816] :
      ( ~ r1_xboole_0(A_815,B_816)
      | v1_xboole_0(k3_xboole_0(A_815,B_816)) ) ),
    inference(resolution,[status(thm)],[c_4,c_13090])).

tff(c_12966,plain,(
    ! [A_792,B_793] :
      ( r2_hidden('#skF_2'(A_792,B_793),A_792)
      | r1_tarski(A_792,B_793) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12971,plain,(
    ! [A_794,B_795] :
      ( ~ v1_xboole_0(A_794)
      | r1_tarski(A_794,B_795) ) ),
    inference(resolution,[status(thm)],[c_12966,c_2])).

tff(c_12986,plain,(
    ! [A_794] :
      ( k1_xboole_0 = A_794
      | ~ v1_xboole_0(A_794) ) ),
    inference(resolution,[status(thm)],[c_12971,c_182])).

tff(c_13110,plain,(
    ! [A_817,B_818] :
      ( k3_xboole_0(A_817,B_818) = k1_xboole_0
      | ~ r1_xboole_0(A_817,B_818) ) ),
    inference(resolution,[status(thm)],[c_13102,c_12986])).

tff(c_13125,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_13110])).

tff(c_13189,plain,(
    ! [A_826,B_827] : k4_xboole_0(A_826,k4_xboole_0(A_826,B_827)) = k3_xboole_0(A_826,B_827) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_13226,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k4_xboole_0(B_28,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_13189])).

tff(c_13233,plain,(
    ! [B_28] : k4_xboole_0(B_28,B_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_13125,c_13226])).

tff(c_13243,plain,(
    ! [B_831] : k3_xboole_0(B_831,B_831) = B_831 ),
    inference(superposition,[status(thm),theory(equality)],[c_13189,c_104])).

tff(c_13100,plain,(
    ! [A_810,B_811] :
      ( ~ r1_xboole_0(A_810,B_811)
      | v1_xboole_0(k3_xboole_0(A_810,B_811)) ) ),
    inference(resolution,[status(thm)],[c_4,c_13090])).

tff(c_13583,plain,(
    ! [B_849] :
      ( ~ r1_xboole_0(B_849,B_849)
      | v1_xboole_0(B_849) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13243,c_13100])).

tff(c_13595,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | k4_xboole_0(A_86,A_86) != A_86 ) ),
    inference(resolution,[status(thm)],[c_155,c_13583])).

tff(c_13610,plain,(
    ! [A_850] :
      ( v1_xboole_0(A_850)
      | k1_xboole_0 != A_850 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13233,c_13595])).

tff(c_12985,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_12971,c_196])).

tff(c_13630,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_13610,c_12985])).

tff(c_12961,plain,(
    ~ r1_tarski('#skF_6','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_12984,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_12971,c_12961])).

tff(c_13631,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_13610,c_12984])).

tff(c_13960,plain,(
    ! [A_887,B_888,C_889,D_890] :
      ( k7_mcart_1(A_887,B_888,C_889,D_890) = k2_mcart_1(D_890)
      | ~ m1_subset_1(D_890,k3_zfmisc_1(A_887,B_888,C_889))
      | k1_xboole_0 = C_889
      | k1_xboole_0 = B_888
      | k1_xboole_0 = A_887 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_13963,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_13960])).

tff(c_13966,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_13630,c_13631,c_13963])).

tff(c_14217,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13966])).

tff(c_13127,plain,(
    ! [B_819,A_820] : k3_xboole_0(B_819,k4_xboole_0(A_820,B_819)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_13110])).

tff(c_16,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,k3_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_13135,plain,(
    ! [B_819,A_820,C_16] :
      ( ~ r1_xboole_0(B_819,k4_xboole_0(A_820,B_819))
      | ~ r2_hidden(C_16,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13127,c_16])).

tff(c_13145,plain,(
    ! [C_16] : ~ r2_hidden(C_16,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_13135])).

tff(c_14247,plain,(
    ! [C_16] : ~ r2_hidden(C_16,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14217,c_13145])).

tff(c_13605,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | k1_xboole_0 != A_86 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13233,c_13595])).

tff(c_13908,plain,(
    ! [C_879,A_880,B_881] :
      ( v1_xboole_0(C_879)
      | ~ m1_subset_1(C_879,k1_zfmisc_1(k2_zfmisc_1(A_880,B_881)))
      | ~ v1_xboole_0(A_880) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_13915,plain,(
    ! [A_32,A_880,B_881] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_880)
      | ~ r2_hidden(A_32,k2_zfmisc_1(A_880,B_881)) ) ),
    inference(resolution,[status(thm)],[c_40,c_13908])).

tff(c_14072,plain,(
    ! [A_897,A_898,B_899] :
      ( ~ v1_xboole_0(A_897)
      | ~ r2_hidden(A_898,k2_zfmisc_1(A_897,B_899)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_13915])).

tff(c_14089,plain,(
    ! [A_900,B_901] :
      ( ~ v1_xboole_0(A_900)
      | v1_xboole_0(k2_zfmisc_1(A_900,B_901)) ) ),
    inference(resolution,[status(thm)],[c_4,c_14072])).

tff(c_14117,plain,(
    ! [A_906,B_907] :
      ( k2_zfmisc_1(A_906,B_907) = k1_xboole_0
      | ~ v1_xboole_0(A_906) ) ),
    inference(resolution,[status(thm)],[c_14089,c_12986])).

tff(c_14130,plain,(
    ! [A_86,B_907] :
      ( k2_zfmisc_1(A_86,B_907) = k1_xboole_0
      | k1_xboole_0 != A_86 ) ),
    inference(resolution,[status(thm)],[c_13605,c_14117])).

tff(c_15413,plain,(
    ! [B_907] : k2_zfmisc_1('#skF_4',B_907) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14217,c_14217,c_14130])).

tff(c_12948,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12943,c_64])).

tff(c_13635,plain,(
    ! [A_852,B_853,C_854] : k2_zfmisc_1(k2_zfmisc_1(A_852,B_853),C_854) = k3_zfmisc_1(A_852,B_853,C_854) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_18367,plain,(
    ! [A_1101,A_1102,B_1103,C_1104] :
      ( r2_hidden(k1_mcart_1(A_1101),k2_zfmisc_1(A_1102,B_1103))
      | ~ r2_hidden(A_1101,k3_zfmisc_1(A_1102,B_1103,C_1104)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13635,c_54])).

tff(c_18391,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_12948,c_18367])).

tff(c_18403,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15413,c_18391])).

tff(c_18405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14247,c_18403])).

tff(c_18407,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13966])).

tff(c_14110,plain,(
    ! [A_902,B_903,C_904,D_905] :
      ( k5_mcart_1(A_902,B_903,C_904,D_905) = k1_mcart_1(k1_mcart_1(D_905))
      | ~ m1_subset_1(D_905,k3_zfmisc_1(A_902,B_903,C_904))
      | k1_xboole_0 = C_904
      | k1_xboole_0 = B_903
      | k1_xboole_0 = A_902 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_14113,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_14110])).

tff(c_14116,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_13630,c_13631,c_14113])).

tff(c_18442,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_18407,c_14116])).

tff(c_24676,plain,(
    ! [A_1353,A_1354,B_1355,C_1356] :
      ( r2_hidden(k1_mcart_1(A_1353),k2_zfmisc_1(A_1354,B_1355))
      | ~ r2_hidden(A_1353,k3_zfmisc_1(A_1354,B_1355,C_1356)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13635,c_54])).

tff(c_24719,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_12948,c_24676])).

tff(c_24736,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_24719,c_54])).

tff(c_24754,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18442,c_24736])).

tff(c_24756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12945,c_24754])).

tff(c_24757,plain,(
    '#skF_6' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_24777,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24757,c_12945])).

tff(c_24846,plain,(
    ! [A_1364,B_1365,C_1366] :
      ( ~ r1_xboole_0(A_1364,B_1365)
      | ~ r2_hidden(C_1366,k3_xboole_0(A_1364,B_1365)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24854,plain,(
    ! [A_1364,B_1365] :
      ( ~ r1_xboole_0(A_1364,B_1365)
      | v1_xboole_0(k3_xboole_0(A_1364,B_1365)) ) ),
    inference(resolution,[status(thm)],[c_4,c_24846])).

tff(c_24897,plain,(
    ! [A_1378,B_1379] :
      ( r2_hidden('#skF_2'(A_1378,B_1379),A_1378)
      | r1_tarski(A_1378,B_1379) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24919,plain,(
    ! [A_1380,B_1381] :
      ( ~ v1_xboole_0(A_1380)
      | r1_tarski(A_1380,B_1381) ) ),
    inference(resolution,[status(thm)],[c_24897,c_2])).

tff(c_24932,plain,(
    ! [A_1382] :
      ( k1_xboole_0 = A_1382
      | ~ v1_xboole_0(A_1382) ) ),
    inference(resolution,[status(thm)],[c_24919,c_182])).

tff(c_25070,plain,(
    ! [A_1400,B_1401] :
      ( k3_xboole_0(A_1400,B_1401) = k1_xboole_0
      | ~ r1_xboole_0(A_1400,B_1401) ) ),
    inference(resolution,[status(thm)],[c_24854,c_24932])).

tff(c_25097,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_25070])).

tff(c_24778,plain,(
    ! [A_1357,B_1358] : k4_xboole_0(A_1357,k4_xboole_0(A_1357,B_1358)) = k3_xboole_0(A_1357,B_1358) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24828,plain,(
    ! [A_1362,B_1363] : r1_xboole_0(k3_xboole_0(A_1362,B_1363),k4_xboole_0(A_1362,B_1363)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24778,c_32])).

tff(c_24842,plain,(
    ! [B_28,A_27] : r1_xboole_0(k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)),B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_24828])).

tff(c_25150,plain,(
    ! [B_1407] : r1_xboole_0(k1_xboole_0,B_1407) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25097,c_24842])).

tff(c_25182,plain,(
    ! [B_1408] : r1_xboole_0(B_1408,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_25150,c_12])).

tff(c_24939,plain,(
    ! [A_1364,B_1365] :
      ( k3_xboole_0(A_1364,B_1365) = k1_xboole_0
      | ~ r1_xboole_0(A_1364,B_1365) ) ),
    inference(resolution,[status(thm)],[c_24854,c_24932])).

tff(c_25205,plain,(
    ! [B_1408] : k3_xboole_0(B_1408,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25182,c_24939])).

tff(c_25239,plain,(
    ! [B_1411] : k4_xboole_0(k1_xboole_0,B_1411) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25150,c_34])).

tff(c_25359,plain,(
    ! [B_1416] : k4_xboole_0(B_1416,k1_xboole_0) = B_1416 ),
    inference(superposition,[status(thm),theory(equality)],[c_25239,c_104])).

tff(c_25384,plain,(
    ! [B_1416] : k4_xboole_0(B_1416,B_1416) = k3_xboole_0(B_1416,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_25359,c_26])).

tff(c_25682,plain,(
    ! [B_1416] : k4_xboole_0(B_1416,B_1416) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25205,c_25384])).

tff(c_24791,plain,(
    ! [B_1358] : k3_xboole_0(B_1358,B_1358) = B_1358 ),
    inference(superposition,[status(thm),theory(equality)],[c_24778,c_104])).

tff(c_24881,plain,(
    ! [A_1374,B_1375] :
      ( ~ r1_xboole_0(A_1374,B_1375)
      | v1_xboole_0(k3_xboole_0(A_1374,B_1375)) ) ),
    inference(resolution,[status(thm)],[c_4,c_24846])).

tff(c_24885,plain,(
    ! [B_1376] :
      ( ~ r1_xboole_0(B_1376,B_1376)
      | v1_xboole_0(B_1376) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24791,c_24881])).

tff(c_24894,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | k4_xboole_0(A_86,A_86) != A_86 ) ),
    inference(resolution,[status(thm)],[c_155,c_24885])).

tff(c_25749,plain,(
    ! [A_1439] :
      ( v1_xboole_0(A_1439)
      | k1_xboole_0 != A_1439 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25682,c_24894])).

tff(c_24929,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24919,c_196])).

tff(c_25766,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_25749,c_24929])).

tff(c_24760,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_5','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24757,c_66])).

tff(c_25850,plain,(
    ! [A_1455,B_1456,C_1457,D_1458] :
      ( k7_mcart_1(A_1455,B_1456,C_1457,D_1458) = k2_mcart_1(D_1458)
      | ~ m1_subset_1(D_1458,k3_zfmisc_1(A_1455,B_1456,C_1457))
      | k1_xboole_0 = C_1457
      | k1_xboole_0 = B_1456
      | k1_xboole_0 = A_1455 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_25853,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24760,c_25850])).

tff(c_25856,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_25766,c_25853])).

tff(c_26079,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_25856])).

tff(c_25683,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | k1_xboole_0 != A_86 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25682,c_24894])).

tff(c_26561,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26079,c_25683])).

tff(c_25472,plain,(
    ! [A_1421,B_1422,C_1423] :
      ( r2_hidden(k1_mcart_1(A_1421),B_1422)
      | ~ r2_hidden(A_1421,k2_zfmisc_1(B_1422,C_1423)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_29319,plain,(
    ! [B_1643,C_1644] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1643,C_1644))),B_1643)
      | v1_xboole_0(k2_zfmisc_1(B_1643,C_1644)) ) ),
    inference(resolution,[status(thm)],[c_4,c_25472])).

tff(c_25801,plain,(
    ! [C_1445,A_1446,B_1447] :
      ( v1_xboole_0(C_1445)
      | ~ m1_subset_1(C_1445,k1_zfmisc_1(k2_zfmisc_1(A_1446,B_1447)))
      | ~ v1_xboole_0(A_1446) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_25808,plain,(
    ! [A_32,A_1446,B_1447] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_1446)
      | ~ r2_hidden(A_32,k2_zfmisc_1(A_1446,B_1447)) ) ),
    inference(resolution,[status(thm)],[c_40,c_25801])).

tff(c_25815,plain,(
    ! [A_1446,A_32,B_1447] :
      ( ~ v1_xboole_0(A_1446)
      | ~ r2_hidden(A_32,k2_zfmisc_1(A_1446,B_1447)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_25808])).

tff(c_29336,plain,(
    ! [A_1446,B_1447,C_1644] :
      ( ~ v1_xboole_0(A_1446)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_1446,B_1447),C_1644)) ) ),
    inference(resolution,[status(thm)],[c_29319,c_25815])).

tff(c_29736,plain,(
    ! [A_1659,B_1660,C_1661] :
      ( ~ v1_xboole_0(A_1659)
      | v1_xboole_0(k3_zfmisc_1(A_1659,B_1660,C_1661)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_29336])).

tff(c_12947,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12943,c_82])).

tff(c_29764,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_29736,c_12947])).

tff(c_29783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26561,c_29764])).

tff(c_29785,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_25856])).

tff(c_25508,plain,(
    ! [C_1425,B_1426,A_1427] :
      ( v1_xboole_0(C_1425)
      | ~ m1_subset_1(C_1425,k1_zfmisc_1(k2_zfmisc_1(B_1426,A_1427)))
      | ~ v1_xboole_0(A_1427) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_25515,plain,(
    ! [A_32,A_1427,B_1426] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_1427)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_1426,A_1427)) ) ),
    inference(resolution,[status(thm)],[c_40,c_25508])).

tff(c_25822,plain,(
    ! [A_1450,A_1451,B_1452] :
      ( ~ v1_xboole_0(A_1450)
      | ~ r2_hidden(A_1451,k2_zfmisc_1(B_1452,A_1450)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_25515])).

tff(c_25836,plain,(
    ! [A_1453,B_1454] :
      ( ~ v1_xboole_0(A_1453)
      | v1_xboole_0(k2_zfmisc_1(B_1454,A_1453)) ) ),
    inference(resolution,[status(thm)],[c_4,c_25822])).

tff(c_29862,plain,(
    ! [C_1668,A_1669,B_1670] :
      ( ~ v1_xboole_0(C_1668)
      | v1_xboole_0(k3_zfmisc_1(A_1669,B_1670,C_1668)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_25836])).

tff(c_29882,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_29862,c_12947])).

tff(c_29893,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(resolution,[status(thm)],[c_25683,c_29882])).

tff(c_25983,plain,(
    ! [A_1469,B_1470,C_1471,D_1472] :
      ( k5_mcart_1(A_1469,B_1470,C_1471,D_1472) = k1_mcart_1(k1_mcart_1(D_1472))
      | ~ m1_subset_1(D_1472,k3_zfmisc_1(A_1469,B_1470,C_1471))
      | k1_xboole_0 = C_1471
      | k1_xboole_0 = B_1470
      | k1_xboole_0 = A_1469 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_25986,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_24760,c_25983])).

tff(c_25989,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_25766,c_25986])).

tff(c_30123,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_29785,c_29893,c_25989])).

tff(c_35242,plain,(
    ! [A_1916,A_1917,B_1918,C_1919] :
      ( r2_hidden(k1_mcart_1(A_1916),k2_zfmisc_1(A_1917,B_1918))
      | ~ r2_hidden(A_1916,k3_zfmisc_1(A_1917,B_1918,C_1919)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_25472])).

tff(c_35285,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_12948,c_35242])).

tff(c_35300,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_35285,c_54])).

tff(c_35319,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30123,c_35300])).

tff(c_35321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24777,c_35319])).

tff(c_35322,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_35324,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35322,c_119])).

tff(c_35536,plain,(
    ! [A_1945,B_1946,C_1947] :
      ( ~ r1_xboole_0(A_1945,B_1946)
      | ~ r2_hidden(C_1947,k3_xboole_0(A_1945,B_1946)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_35559,plain,(
    ! [A_1950,B_1951] :
      ( ~ r1_xboole_0(A_1950,B_1951)
      | v1_xboole_0(k3_xboole_0(A_1950,B_1951)) ) ),
    inference(resolution,[status(thm)],[c_4,c_35536])).

tff(c_35362,plain,(
    ! [A_1925,B_1926] :
      ( r2_hidden('#skF_2'(A_1925,B_1926),A_1925)
      | r1_tarski(A_1925,B_1926) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35373,plain,(
    ! [A_1927,B_1928] :
      ( ~ v1_xboole_0(A_1927)
      | r1_tarski(A_1927,B_1928) ) ),
    inference(resolution,[status(thm)],[c_35362,c_2])).

tff(c_35388,plain,(
    ! [A_1927] :
      ( k1_xboole_0 = A_1927
      | ~ v1_xboole_0(A_1927) ) ),
    inference(resolution,[status(thm)],[c_35373,c_182])).

tff(c_35613,plain,(
    ! [A_1958,B_1959] :
      ( k3_xboole_0(A_1958,B_1959) = k1_xboole_0
      | ~ r1_xboole_0(A_1958,B_1959) ) ),
    inference(resolution,[status(thm)],[c_35559,c_35388])).

tff(c_35657,plain,(
    ! [B_1963,A_1964] : k3_xboole_0(B_1963,k4_xboole_0(A_1964,B_1963)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_35613])).

tff(c_35443,plain,(
    ! [A_1936,B_1937] : k4_xboole_0(A_1936,k4_xboole_0(A_1936,B_1937)) = k3_xboole_0(A_1936,B_1937) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_35488,plain,(
    ! [A_1939,B_1940] : r1_xboole_0(k3_xboole_0(A_1939,B_1940),k4_xboole_0(A_1939,B_1940)) ),
    inference(superposition,[status(thm),theory(equality)],[c_35443,c_32])).

tff(c_35508,plain,(
    ! [A_1939,B_1940] : r1_xboole_0(k4_xboole_0(A_1939,B_1940),k3_xboole_0(A_1939,B_1940)) ),
    inference(resolution,[status(thm)],[c_35488,c_12])).

tff(c_35662,plain,(
    ! [B_1963,A_1964] : r1_xboole_0(k4_xboole_0(B_1963,k4_xboole_0(A_1964,B_1963)),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_35657,c_35508])).

tff(c_35688,plain,(
    ! [B_1965] : r1_xboole_0(B_1965,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_35662])).

tff(c_35569,plain,(
    ! [A_1950,B_1951] :
      ( k3_xboole_0(A_1950,B_1951) = k1_xboole_0
      | ~ r1_xboole_0(A_1950,B_1951) ) ),
    inference(resolution,[status(thm)],[c_35559,c_35388])).

tff(c_35711,plain,(
    ! [B_1965] : k3_xboole_0(B_1965,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35688,c_35569])).

tff(c_35774,plain,(
    ! [B_1971] : k4_xboole_0(B_1971,k1_xboole_0) = B_1971 ),
    inference(resolution,[status(thm)],[c_35688,c_34])).

tff(c_35795,plain,(
    ! [B_1971] : k4_xboole_0(B_1971,B_1971) = k3_xboole_0(B_1971,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_35774,c_26])).

tff(c_36132,plain,(
    ! [B_1971] : k4_xboole_0(B_1971,B_1971) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35711,c_35795])).

tff(c_35456,plain,(
    ! [B_1937] : k3_xboole_0(B_1937,B_1937) = B_1937 ),
    inference(superposition,[status(thm),theory(equality)],[c_35443,c_104])).

tff(c_35570,plain,(
    ! [B_1952] :
      ( ~ r1_xboole_0(B_1952,B_1952)
      | v1_xboole_0(B_1952) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35456,c_35559])).

tff(c_35580,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k4_xboole_0(B_30,B_30) != B_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_35570])).

tff(c_36199,plain,(
    ! [B_1991] :
      ( v1_xboole_0(B_1991)
      | k1_xboole_0 != B_1991 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36132,c_35580])).

tff(c_35340,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_35386,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_35373,c_35340])).

tff(c_36220,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_36199,c_35386])).

tff(c_35339,plain,(
    ~ r1_tarski('#skF_6','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_35387,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_35373,c_35339])).

tff(c_36219,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_36199,c_35387])).

tff(c_35326,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35322,c_66])).

tff(c_36562,plain,(
    ! [A_2030,B_2031,C_2032,D_2033] :
      ( k7_mcart_1(A_2030,B_2031,C_2032,D_2033) = k2_mcart_1(D_2033)
      | ~ m1_subset_1(D_2033,k3_zfmisc_1(A_2030,B_2031,C_2032))
      | k1_xboole_0 = C_2032
      | k1_xboole_0 = B_2031
      | k1_xboole_0 = A_2030 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36565,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_35326,c_36562])).

tff(c_36568,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_36220,c_36219,c_36565])).

tff(c_36698,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_36568])).

tff(c_36133,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k1_xboole_0 != B_30 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36132,c_35580])).

tff(c_36714,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | B_30 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36698,c_36133])).

tff(c_36372,plain,(
    ! [C_2007,B_2008,A_2009] :
      ( v1_xboole_0(C_2007)
      | ~ m1_subset_1(C_2007,k1_zfmisc_1(k2_zfmisc_1(B_2008,A_2009)))
      | ~ v1_xboole_0(A_2009) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36379,plain,(
    ! [A_32,A_2009,B_2008] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_2009)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_2008,A_2009)) ) ),
    inference(resolution,[status(thm)],[c_40,c_36372])).

tff(c_36418,plain,(
    ! [A_2011,A_2012,B_2013] :
      ( ~ v1_xboole_0(A_2011)
      | ~ r2_hidden(A_2012,k2_zfmisc_1(B_2013,A_2011)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36379])).

tff(c_36431,plain,(
    ! [A_2011,B_2013] :
      ( ~ v1_xboole_0(A_2011)
      | v1_xboole_0(k2_zfmisc_1(B_2013,A_2011)) ) ),
    inference(resolution,[status(thm)],[c_4,c_36418])).

tff(c_36446,plain,(
    ! [C_2016,A_2017,B_2018] :
      ( v1_xboole_0(C_2016)
      | ~ m1_subset_1(C_2016,k1_zfmisc_1(k2_zfmisc_1(A_2017,B_2018)))
      | ~ v1_xboole_0(A_2017) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36453,plain,(
    ! [A_32,A_2017,B_2018] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_2017)
      | ~ r2_hidden(A_32,k2_zfmisc_1(A_2017,B_2018)) ) ),
    inference(resolution,[status(thm)],[c_40,c_36446])).

tff(c_36509,plain,(
    ! [A_2023,A_2024,B_2025] :
      ( ~ v1_xboole_0(A_2023)
      | ~ r2_hidden(A_2024,k2_zfmisc_1(A_2023,B_2025)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36453])).

tff(c_36526,plain,(
    ! [A_2026,B_2027] :
      ( ~ v1_xboole_0(A_2026)
      | v1_xboole_0(k2_zfmisc_1(A_2026,B_2027)) ) ),
    inference(resolution,[status(thm)],[c_4,c_36509])).

tff(c_36547,plain,(
    ! [A_2028,B_2029] :
      ( k2_zfmisc_1(A_2028,B_2029) = k1_xboole_0
      | ~ v1_xboole_0(A_2028) ) ),
    inference(resolution,[status(thm)],[c_36526,c_35388])).

tff(c_36551,plain,(
    ! [B_2013,A_2011,B_2029] :
      ( k2_zfmisc_1(k2_zfmisc_1(B_2013,A_2011),B_2029) = k1_xboole_0
      | ~ v1_xboole_0(A_2011) ) ),
    inference(resolution,[status(thm)],[c_36431,c_36547])).

tff(c_36559,plain,(
    ! [B_2013,A_2011,B_2029] :
      ( k3_zfmisc_1(B_2013,A_2011,B_2029) = k1_xboole_0
      | ~ v1_xboole_0(A_2011) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_36551])).

tff(c_39060,plain,(
    ! [B_2161,A_2162,B_2163] :
      ( k3_zfmisc_1(B_2161,A_2162,B_2163) = '#skF_8'
      | ~ v1_xboole_0(A_2162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36698,c_36559])).

tff(c_40074,plain,(
    ! [B_2161,B_2163] : k3_zfmisc_1(B_2161,'#skF_8',B_2163) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_36714,c_39060])).

tff(c_36221,plain,(
    k3_zfmisc_1('#skF_7','#skF_8','#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36199,c_82])).

tff(c_36710,plain,(
    k3_zfmisc_1('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36698,c_36221])).

tff(c_40082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40074,c_36710])).

tff(c_40084,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_36568])).

tff(c_40283,plain,(
    ! [A_2242,B_2243,C_2244,D_2245] :
      ( k5_mcart_1(A_2242,B_2243,C_2244,D_2245) = k1_mcart_1(k1_mcart_1(D_2245))
      | ~ m1_subset_1(D_2245,k3_zfmisc_1(A_2242,B_2243,C_2244))
      | k1_xboole_0 = C_2244
      | k1_xboole_0 = B_2243
      | k1_xboole_0 = A_2242 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40286,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_35326,c_40283])).

tff(c_40289,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_36220,c_40084,c_36219,c_40286])).

tff(c_36121,plain,(
    ! [A_1987,B_1988,C_1989] :
      ( r2_hidden(k1_mcart_1(A_1987),B_1988)
      | ~ r2_hidden(A_1987,k2_zfmisc_1(B_1988,C_1989)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_45897,plain,(
    ! [A_2471,A_2472,B_2473,C_2474] :
      ( r2_hidden(k1_mcart_1(A_2471),k2_zfmisc_1(A_2472,B_2473))
      | ~ r2_hidden(A_2471,k3_zfmisc_1(A_2472,B_2473,C_2474)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_36121])).

tff(c_45941,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_45897])).

tff(c_46017,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_45941,c_54])).

tff(c_46036,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40289,c_46017])).

tff(c_46038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35324,c_46036])).

tff(c_46039,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_46086,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46039,c_35324])).

tff(c_46316,plain,(
    ! [A_2510,B_2511,C_2512] :
      ( ~ r1_xboole_0(A_2510,B_2511)
      | ~ r2_hidden(C_2512,k3_xboole_0(A_2510,B_2511)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46339,plain,(
    ! [A_2515,B_2516] :
      ( ~ r1_xboole_0(A_2515,B_2516)
      | v1_xboole_0(k3_xboole_0(A_2515,B_2516)) ) ),
    inference(resolution,[status(thm)],[c_4,c_46316])).

tff(c_46210,plain,(
    ! [A_2495,B_2496] :
      ( r2_hidden('#skF_2'(A_2495,B_2496),A_2495)
      | r1_tarski(A_2495,B_2496) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46221,plain,(
    ! [A_2497,B_2498] :
      ( ~ v1_xboole_0(A_2497)
      | r1_tarski(A_2497,B_2498) ) ),
    inference(resolution,[status(thm)],[c_46210,c_2])).

tff(c_46237,plain,(
    ! [A_2497] :
      ( k1_xboole_0 = A_2497
      | ~ v1_xboole_0(A_2497) ) ),
    inference(resolution,[status(thm)],[c_46221,c_182])).

tff(c_46372,plain,(
    ! [A_2522,B_2523] :
      ( k3_xboole_0(A_2522,B_2523) = k1_xboole_0
      | ~ r1_xboole_0(A_2522,B_2523) ) ),
    inference(resolution,[status(thm)],[c_46339,c_46237])).

tff(c_46403,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_46372])).

tff(c_46087,plain,(
    ! [A_2481,B_2482] : k4_xboole_0(A_2481,k4_xboole_0(A_2481,B_2482)) = k3_xboole_0(A_2481,B_2482) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_46157,plain,(
    ! [A_2486,B_2487] : r1_xboole_0(k4_xboole_0(A_2486,B_2487),k3_xboole_0(A_2486,B_2487)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46087,c_91])).

tff(c_46174,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_46157])).

tff(c_46438,plain,(
    ! [B_2526] : r1_xboole_0(B_2526,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46403,c_46174])).

tff(c_46349,plain,(
    ! [A_2515,B_2516] :
      ( k3_xboole_0(A_2515,B_2516) = k1_xboole_0
      | ~ r1_xboole_0(A_2515,B_2516) ) ),
    inference(resolution,[status(thm)],[c_46339,c_46237])).

tff(c_46457,plain,(
    ! [B_2526] : k3_xboole_0(B_2526,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46438,c_46349])).

tff(c_46590,plain,(
    ! [B_2537] : k4_xboole_0(B_2537,k1_xboole_0) = B_2537 ),
    inference(resolution,[status(thm)],[c_46438,c_34])).

tff(c_46608,plain,(
    ! [B_2537] : k4_xboole_0(B_2537,B_2537) = k3_xboole_0(B_2537,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46590,c_26])).

tff(c_46893,plain,(
    ! [B_2537] : k4_xboole_0(B_2537,B_2537) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46457,c_46608])).

tff(c_46103,plain,(
    ! [B_2482] : k3_xboole_0(B_2482,B_2482) = B_2482 ),
    inference(superposition,[status(thm),theory(equality)],[c_46087,c_104])).

tff(c_46350,plain,(
    ! [B_2517] :
      ( ~ r1_xboole_0(B_2517,B_2517)
      | v1_xboole_0(B_2517) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46103,c_46339])).

tff(c_46359,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | k4_xboole_0(A_86,A_86) != A_86 ) ),
    inference(resolution,[status(thm)],[c_155,c_46350])).

tff(c_46976,plain,(
    ! [A_2555] :
      ( v1_xboole_0(A_2555)
      | k1_xboole_0 != A_2555 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46893,c_46359])).

tff(c_46236,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46221,c_35339])).

tff(c_46993,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_46976,c_46236])).

tff(c_47257,plain,(
    ! [A_2588,B_2589,C_2590,D_2591] :
      ( k7_mcart_1(A_2588,B_2589,C_2590,D_2591) = k2_mcart_1(D_2591)
      | ~ m1_subset_1(D_2591,k3_zfmisc_1(A_2588,B_2589,C_2590))
      | k1_xboole_0 = C_2590
      | k1_xboole_0 = B_2589
      | k1_xboole_0 = A_2588 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_47260,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_35326,c_47257])).

tff(c_47263,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46993,c_47260])).

tff(c_47379,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_47263])).

tff(c_46894,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | k1_xboole_0 != A_86 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46893,c_46359])).

tff(c_47813,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47379,c_46894])).

tff(c_46753,plain,(
    ! [A_2540,B_2541,C_2542] :
      ( r2_hidden(k1_mcart_1(A_2540),B_2541)
      | ~ r2_hidden(A_2540,k2_zfmisc_1(B_2541,C_2542)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50975,plain,(
    ! [B_2778,C_2779] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2778,C_2779))),B_2778)
      | v1_xboole_0(k2_zfmisc_1(B_2778,C_2779)) ) ),
    inference(resolution,[status(thm)],[c_4,c_46753])).

tff(c_47069,plain,(
    ! [C_2565,A_2566,B_2567] :
      ( v1_xboole_0(C_2565)
      | ~ m1_subset_1(C_2565,k1_zfmisc_1(k2_zfmisc_1(A_2566,B_2567)))
      | ~ v1_xboole_0(A_2566) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_47076,plain,(
    ! [A_32,A_2566,B_2567] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_2566)
      | ~ r2_hidden(A_32,k2_zfmisc_1(A_2566,B_2567)) ) ),
    inference(resolution,[status(thm)],[c_40,c_47069])).

tff(c_47083,plain,(
    ! [A_2566,A_32,B_2567] :
      ( ~ v1_xboole_0(A_2566)
      | ~ r2_hidden(A_32,k2_zfmisc_1(A_2566,B_2567)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_47076])).

tff(c_50992,plain,(
    ! [A_2566,B_2567,C_2779] :
      ( ~ v1_xboole_0(A_2566)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_2566,B_2567),C_2779)) ) ),
    inference(resolution,[status(thm)],[c_50975,c_47083])).

tff(c_51089,plain,(
    ! [A_2782,B_2783,C_2784] :
      ( ~ v1_xboole_0(A_2782)
      | v1_xboole_0(k3_zfmisc_1(A_2782,B_2783,C_2784)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50992])).

tff(c_46042,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46039,c_82])).

tff(c_51117,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_51089,c_46042])).

tff(c_51133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47813,c_51117])).

tff(c_51135,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_47263])).

tff(c_51238,plain,(
    ! [A_2794,B_2795,C_2796,D_2797] :
      ( k5_mcart_1(A_2794,B_2795,C_2796,D_2797) = k1_mcart_1(k1_mcart_1(D_2797))
      | ~ m1_subset_1(D_2797,k3_zfmisc_1(A_2794,B_2795,C_2796))
      | k1_xboole_0 = C_2796
      | k1_xboole_0 = B_2795
      | k1_xboole_0 = A_2794 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_51241,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_35326,c_51238])).

tff(c_51244,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_51135,c_46993,c_51241])).

tff(c_51281,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_51244])).

tff(c_51818,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51281,c_46894])).

tff(c_54182,plain,(
    ! [B_2945,C_2946] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2945,C_2946))),B_2945)
      | v1_xboole_0(k2_zfmisc_1(B_2945,C_2946)) ) ),
    inference(resolution,[status(thm)],[c_4,c_46753])).

tff(c_46958,plain,(
    ! [C_2552,B_2553,A_2554] :
      ( v1_xboole_0(C_2552)
      | ~ m1_subset_1(C_2552,k1_zfmisc_1(k2_zfmisc_1(B_2553,A_2554)))
      | ~ v1_xboole_0(A_2554) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46965,plain,(
    ! [A_32,A_2554,B_2553] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_2554)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_2553,A_2554)) ) ),
    inference(resolution,[status(thm)],[c_40,c_46958])).

tff(c_46972,plain,(
    ! [A_2554,A_32,B_2553] :
      ( ~ v1_xboole_0(A_2554)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_2553,A_2554)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_46965])).

tff(c_54203,plain,(
    ! [A_2554,B_2553,C_2946] :
      ( ~ v1_xboole_0(A_2554)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_2553,A_2554),C_2946)) ) ),
    inference(resolution,[status(thm)],[c_54182,c_46972])).

tff(c_54845,plain,(
    ! [A_2967,B_2968,C_2969] :
      ( ~ v1_xboole_0(A_2967)
      | v1_xboole_0(k3_zfmisc_1(B_2968,A_2967,C_2969)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_54203])).

tff(c_54873,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_54845,c_46042])).

tff(c_54889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51818,c_54873])).

tff(c_54890,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_51244])).

tff(c_46043,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46039,c_64])).

tff(c_60895,plain,(
    ! [A_3216,A_3217,B_3218,C_3219] :
      ( r2_hidden(k1_mcart_1(A_3216),k2_zfmisc_1(A_3217,B_3218))
      | ~ r2_hidden(A_3216,k3_zfmisc_1(A_3217,B_3218,C_3219)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_46753])).

tff(c_60938,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_46043,c_60895])).

tff(c_60953,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_60938,c_54])).

tff(c_60972,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54890,c_60953])).

tff(c_60974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46086,c_60972])).

tff(c_60975,plain,(
    '#skF_6' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_60992,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60975,c_35324])).

tff(c_61020,plain,(
    ! [A_3226,B_3227,C_3228] :
      ( ~ r1_xboole_0(A_3226,B_3227)
      | ~ r2_hidden(C_3228,k3_xboole_0(A_3226,B_3227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61025,plain,(
    ! [A_3226,B_3227] :
      ( ~ r1_xboole_0(A_3226,B_3227)
      | v1_xboole_0(k3_xboole_0(A_3226,B_3227)) ) ),
    inference(resolution,[status(thm)],[c_4,c_61020])).

tff(c_61094,plain,(
    ! [A_3240,B_3241] :
      ( r2_hidden('#skF_2'(A_3240,B_3241),A_3240)
      | r1_tarski(A_3240,B_3241) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_61132,plain,(
    ! [A_3243,B_3244] :
      ( ~ v1_xboole_0(A_3243)
      | r1_tarski(A_3243,B_3244) ) ),
    inference(resolution,[status(thm)],[c_61094,c_2])).

tff(c_61150,plain,(
    ! [A_3245] :
      ( k1_xboole_0 = A_3245
      | ~ v1_xboole_0(A_3245) ) ),
    inference(resolution,[status(thm)],[c_61132,c_182])).

tff(c_61282,plain,(
    ! [A_3264,B_3265] :
      ( k3_xboole_0(A_3264,B_3265) = k1_xboole_0
      | ~ r1_xboole_0(A_3264,B_3265) ) ),
    inference(resolution,[status(thm)],[c_61025,c_61150])).

tff(c_61307,plain,(
    ! [B_3266,A_3267] : k3_xboole_0(B_3266,k4_xboole_0(A_3267,B_3266)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_61282])).

tff(c_61056,plain,(
    ! [A_3238,B_3239] : k4_xboole_0(A_3238,k4_xboole_0(A_3238,B_3239)) = k3_xboole_0(A_3238,B_3239) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_61190,plain,(
    ! [A_3253,B_3254] : r1_xboole_0(k3_xboole_0(A_3253,B_3254),k4_xboole_0(A_3253,B_3254)) ),
    inference(superposition,[status(thm),theory(equality)],[c_61056,c_32])).

tff(c_61210,plain,(
    ! [A_3253,B_3254] : r1_xboole_0(k4_xboole_0(A_3253,B_3254),k3_xboole_0(A_3253,B_3254)) ),
    inference(resolution,[status(thm)],[c_61190,c_12])).

tff(c_61312,plain,(
    ! [B_3266,A_3267] : r1_xboole_0(k4_xboole_0(B_3266,k4_xboole_0(A_3267,B_3266)),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_61307,c_61210])).

tff(c_61338,plain,(
    ! [B_3268] : r1_xboole_0(B_3268,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_61312])).

tff(c_61157,plain,(
    ! [A_3226,B_3227] :
      ( k3_xboole_0(A_3226,B_3227) = k1_xboole_0
      | ~ r1_xboole_0(A_3226,B_3227) ) ),
    inference(resolution,[status(thm)],[c_61025,c_61150])).

tff(c_61357,plain,(
    ! [B_3268] : k3_xboole_0(B_3268,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61338,c_61157])).

tff(c_61428,plain,(
    ! [B_3277] : k4_xboole_0(B_3277,k1_xboole_0) = B_3277 ),
    inference(resolution,[status(thm)],[c_61338,c_34])).

tff(c_61446,plain,(
    ! [B_3277] : k4_xboole_0(B_3277,B_3277) = k3_xboole_0(B_3277,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_61428,c_26])).

tff(c_61827,plain,(
    ! [B_3277] : k4_xboole_0(B_3277,B_3277) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61357,c_61446])).

tff(c_61116,plain,(
    ! [B_3242] : k3_xboole_0(B_3242,B_3242) = B_3242 ),
    inference(superposition,[status(thm),theory(equality)],[c_61056,c_104])).

tff(c_61160,plain,(
    ! [B_3246] :
      ( ~ r1_xboole_0(B_3246,B_3246)
      | v1_xboole_0(B_3246) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61116,c_61025])).

tff(c_61169,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | k4_xboole_0(A_86,A_86) != A_86 ) ),
    inference(resolution,[status(thm)],[c_155,c_61160])).

tff(c_61894,plain,(
    ! [A_3296] :
      ( v1_xboole_0(A_3296)
      | k1_xboole_0 != A_3296 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61827,c_61169])).

tff(c_60990,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_61147,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_61132,c_60990])).

tff(c_61911,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_61894,c_61147])).

tff(c_60991,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60975,c_35326])).

tff(c_61931,plain,(
    ! [A_3301,B_3302,C_3303,D_3304] :
      ( k7_mcart_1(A_3301,B_3302,C_3303,D_3304) = k2_mcart_1(D_3304)
      | ~ m1_subset_1(D_3304,k3_zfmisc_1(A_3301,B_3302,C_3303))
      | k1_xboole_0 = C_3303
      | k1_xboole_0 = B_3302
      | k1_xboole_0 = A_3301 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_61934,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60991,c_61931])).

tff(c_61937,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_61911,c_61934])).

tff(c_62040,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_61937])).

tff(c_61828,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | k1_xboole_0 != A_86 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61827,c_61169])).

tff(c_62052,plain,(
    ! [A_86] :
      ( v1_xboole_0(A_86)
      | A_86 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62040,c_61828])).

tff(c_61729,plain,(
    ! [C_3288,B_3289,A_3290] :
      ( v1_xboole_0(C_3288)
      | ~ m1_subset_1(C_3288,k1_zfmisc_1(k2_zfmisc_1(B_3289,A_3290)))
      | ~ v1_xboole_0(A_3290) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_61736,plain,(
    ! [A_32,A_3290,B_3289] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_3290)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_3289,A_3290)) ) ),
    inference(resolution,[status(thm)],[c_40,c_61729])).

tff(c_62026,plain,(
    ! [A_3319,A_3320,B_3321] :
      ( ~ v1_xboole_0(A_3319)
      | ~ r2_hidden(A_3320,k2_zfmisc_1(B_3321,A_3319)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_61736])).

tff(c_62039,plain,(
    ! [A_3319,B_3321] :
      ( ~ v1_xboole_0(A_3319)
      | v1_xboole_0(k2_zfmisc_1(B_3321,A_3319)) ) ),
    inference(resolution,[status(thm)],[c_4,c_62026])).

tff(c_61914,plain,(
    ! [C_3297,A_3298,B_3299] :
      ( v1_xboole_0(C_3297)
      | ~ m1_subset_1(C_3297,k1_zfmisc_1(k2_zfmisc_1(A_3298,B_3299)))
      | ~ v1_xboole_0(A_3298) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_61921,plain,(
    ! [A_32,A_3298,B_3299] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_3298)
      | ~ r2_hidden(A_32,k2_zfmisc_1(A_3298,B_3299)) ) ),
    inference(resolution,[status(thm)],[c_40,c_61914])).

tff(c_62181,plain,(
    ! [A_3332,A_3333,B_3334] :
      ( ~ v1_xboole_0(A_3332)
      | ~ r2_hidden(A_3333,k2_zfmisc_1(A_3332,B_3334)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_61921])).

tff(c_62610,plain,(
    ! [A_3351,B_3352] :
      ( ~ v1_xboole_0(A_3351)
      | v1_xboole_0(k2_zfmisc_1(A_3351,B_3352)) ) ),
    inference(resolution,[status(thm)],[c_4,c_62181])).

tff(c_61148,plain,(
    ! [A_3243] :
      ( k1_xboole_0 = A_3243
      | ~ v1_xboole_0(A_3243) ) ),
    inference(resolution,[status(thm)],[c_61132,c_182])).

tff(c_62066,plain,(
    ! [A_3243] :
      ( A_3243 = '#skF_8'
      | ~ v1_xboole_0(A_3243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62040,c_61148])).

tff(c_62857,plain,(
    ! [A_3363,B_3364] :
      ( k2_zfmisc_1(A_3363,B_3364) = '#skF_8'
      | ~ v1_xboole_0(A_3363) ) ),
    inference(resolution,[status(thm)],[c_62610,c_62066])).

tff(c_62861,plain,(
    ! [B_3321,A_3319,B_3364] :
      ( k2_zfmisc_1(k2_zfmisc_1(B_3321,A_3319),B_3364) = '#skF_8'
      | ~ v1_xboole_0(A_3319) ) ),
    inference(resolution,[status(thm)],[c_62039,c_62857])).

tff(c_64473,plain,(
    ! [B_3456,A_3457,B_3458] :
      ( k3_zfmisc_1(B_3456,A_3457,B_3458) = '#skF_8'
      | ~ v1_xboole_0(A_3457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_62861])).

tff(c_65053,plain,(
    ! [B_3456,B_3458] : k3_zfmisc_1(B_3456,'#skF_8',B_3458) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_62052,c_64473])).

tff(c_61912,plain,(
    k3_zfmisc_1('#skF_7','#skF_8','#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61894,c_82])).

tff(c_62049,plain,(
    k3_zfmisc_1('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62040,c_61912])).

tff(c_65061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65053,c_62049])).

tff(c_65063,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_61937])).

tff(c_65078,plain,(
    ! [A_3491,B_3492,C_3493,D_3494] :
      ( k5_mcart_1(A_3491,B_3492,C_3493,D_3494) = k1_mcart_1(k1_mcart_1(D_3494))
      | ~ m1_subset_1(D_3494,k3_zfmisc_1(A_3491,B_3492,C_3493))
      | k1_xboole_0 = C_3493
      | k1_xboole_0 = B_3492
      | k1_xboole_0 = A_3491 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_65081,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60991,c_65078])).

tff(c_65084,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_61911,c_65063,c_65081])).

tff(c_65164,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_65084])).

tff(c_65648,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65164,c_61828])).

tff(c_65064,plain,(
    ! [A_3489,B_3490] :
      ( ~ v1_xboole_0(A_3489)
      | v1_xboole_0(k2_zfmisc_1(B_3490,A_3489)) ) ),
    inference(resolution,[status(thm)],[c_4,c_62026])).

tff(c_67352,plain,(
    ! [C_3607,A_3608,B_3609] :
      ( ~ v1_xboole_0(C_3607)
      | v1_xboole_0(k3_zfmisc_1(A_3608,B_3609,C_3607)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_65064])).

tff(c_67370,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_67352,c_82])).

tff(c_67381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65648,c_67370])).

tff(c_67382,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_65084])).

tff(c_61241,plain,(
    ! [A_3259,B_3260,C_3261] : k2_zfmisc_1(k2_zfmisc_1(A_3259,B_3260),C_3261) = k3_zfmisc_1(A_3259,B_3260,C_3261) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_72327,plain,(
    ! [A_3837,A_3838,B_3839,C_3840] :
      ( r2_hidden(k1_mcart_1(A_3837),k2_zfmisc_1(A_3838,B_3839))
      | ~ r2_hidden(A_3837,k3_zfmisc_1(A_3838,B_3839,C_3840)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61241,c_54])).

tff(c_72368,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_72327])).

tff(c_72386,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_72368,c_54])).

tff(c_72404,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67382,c_72386])).

tff(c_72406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60992,c_72404])).

tff(c_72407,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_72429,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72407,c_60975,c_35324])).

tff(c_72424,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60975,c_35326])).

tff(c_73405,plain,(
    ! [A_3926,B_3927,C_3928,D_3929] :
      ( k7_mcart_1(A_3926,B_3927,C_3928,D_3929) = k2_mcart_1(D_3929)
      | ~ m1_subset_1(D_3929,k3_zfmisc_1(A_3926,B_3927,C_3928))
      | k1_xboole_0 = C_3928
      | k1_xboole_0 = B_3927
      | k1_xboole_0 = A_3926 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_73409,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_72424,c_73405])).

tff(c_73510,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_73409])).

tff(c_72431,plain,(
    ! [A_3843,B_3844,C_3845] :
      ( ~ r1_xboole_0(A_3843,B_3844)
      | ~ r2_hidden(C_3845,k3_xboole_0(A_3843,B_3844)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72436,plain,(
    ! [A_3843,B_3844] :
      ( ~ r1_xboole_0(A_3843,B_3844)
      | v1_xboole_0(k3_xboole_0(A_3843,B_3844)) ) ),
    inference(resolution,[status(thm)],[c_4,c_72431])).

tff(c_72521,plain,(
    ! [A_3857,B_3858] :
      ( r2_hidden('#skF_2'(A_3857,B_3858),A_3857)
      | r1_tarski(A_3857,B_3858) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72543,plain,(
    ! [A_3859,B_3860] :
      ( ~ v1_xboole_0(A_3859)
      | r1_tarski(A_3859,B_3860) ) ),
    inference(resolution,[status(thm)],[c_72521,c_2])).

tff(c_72552,plain,(
    ! [A_3861] :
      ( k1_xboole_0 = A_3861
      | ~ v1_xboole_0(A_3861) ) ),
    inference(resolution,[status(thm)],[c_72543,c_182])).

tff(c_72749,plain,(
    ! [A_3889,B_3890] :
      ( k3_xboole_0(A_3889,B_3890) = k1_xboole_0
      | ~ r1_xboole_0(A_3889,B_3890) ) ),
    inference(resolution,[status(thm)],[c_72436,c_72552])).

tff(c_72780,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_72749])).

tff(c_72452,plain,(
    ! [A_3852,B_3853] : k4_xboole_0(A_3852,k4_xboole_0(A_3852,B_3853)) = k3_xboole_0(A_3852,B_3853) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_72589,plain,(
    ! [A_3867,B_3868] : r1_xboole_0(k3_xboole_0(A_3867,B_3868),k4_xboole_0(A_3867,B_3868)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72452,c_32])).

tff(c_72651,plain,(
    ! [A_3876,B_3877] : r1_xboole_0(k4_xboole_0(A_3876,B_3877),k3_xboole_0(A_3876,B_3877)) ),
    inference(resolution,[status(thm)],[c_72589,c_12])).

tff(c_72668,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_72651])).

tff(c_72825,plain,(
    ! [B_3896] : r1_xboole_0(B_3896,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72780,c_72668])).

tff(c_72561,plain,(
    ! [A_3843,B_3844] :
      ( k3_xboole_0(A_3843,B_3844) = k1_xboole_0
      | ~ r1_xboole_0(A_3843,B_3844) ) ),
    inference(resolution,[status(thm)],[c_72436,c_72552])).

tff(c_72844,plain,(
    ! [B_3896] : k3_xboole_0(B_3896,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72825,c_72561])).

tff(c_72934,plain,(
    ! [B_3903] : k4_xboole_0(B_3903,k1_xboole_0) = B_3903 ),
    inference(resolution,[status(thm)],[c_72825,c_34])).

tff(c_72955,plain,(
    ! [B_3903] : k4_xboole_0(B_3903,B_3903) = k3_xboole_0(B_3903,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_72934,c_26])).

tff(c_73305,plain,(
    ! [B_3903] : k4_xboole_0(B_3903,B_3903) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72844,c_72955])).

tff(c_72487,plain,(
    ! [B_3854] : k3_xboole_0(B_3854,B_3854) = B_3854 ),
    inference(superposition,[status(thm),theory(equality)],[c_72452,c_104])).

tff(c_72503,plain,(
    ! [B_3855] :
      ( ~ r1_xboole_0(B_3855,B_3855)
      | v1_xboole_0(B_3855) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72487,c_72436])).

tff(c_72513,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k4_xboole_0(B_30,B_30) != B_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_72503])).

tff(c_73306,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k1_xboole_0 != B_30 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73305,c_72513])).

tff(c_73521,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | B_30 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73510,c_73306])).

tff(c_73151,plain,(
    ! [C_3910,A_3911,B_3912] :
      ( v1_xboole_0(C_3910)
      | ~ m1_subset_1(C_3910,k1_zfmisc_1(k2_zfmisc_1(A_3911,B_3912)))
      | ~ v1_xboole_0(A_3911) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_73158,plain,(
    ! [A_32,A_3911,B_3912] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_3911)
      | ~ r2_hidden(A_32,k2_zfmisc_1(A_3911,B_3912)) ) ),
    inference(resolution,[status(thm)],[c_40,c_73151])).

tff(c_73496,plain,(
    ! [A_3944,A_3945,B_3946] :
      ( ~ v1_xboole_0(A_3944)
      | ~ r2_hidden(A_3945,k2_zfmisc_1(A_3944,B_3946)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_73158])).

tff(c_73509,plain,(
    ! [A_3944,B_3946] :
      ( ~ v1_xboole_0(A_3944)
      | v1_xboole_0(k2_zfmisc_1(A_3944,B_3946)) ) ),
    inference(resolution,[status(thm)],[c_4,c_73496])).

tff(c_74115,plain,(
    ! [A_3975,B_3976] :
      ( ~ v1_xboole_0(A_3975)
      | v1_xboole_0(k2_zfmisc_1(A_3975,B_3976)) ) ),
    inference(resolution,[status(thm)],[c_4,c_73496])).

tff(c_72550,plain,(
    ! [A_3859] :
      ( k1_xboole_0 = A_3859
      | ~ v1_xboole_0(A_3859) ) ),
    inference(resolution,[status(thm)],[c_72543,c_182])).

tff(c_73535,plain,(
    ! [A_3859] :
      ( A_3859 = '#skF_4'
      | ~ v1_xboole_0(A_3859) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73510,c_72550])).

tff(c_74402,plain,(
    ! [A_3992,B_3993] :
      ( k2_zfmisc_1(A_3992,B_3993) = '#skF_4'
      | ~ v1_xboole_0(A_3992) ) ),
    inference(resolution,[status(thm)],[c_74115,c_73535])).

tff(c_74404,plain,(
    ! [A_3944,B_3946,B_3993] :
      ( k2_zfmisc_1(k2_zfmisc_1(A_3944,B_3946),B_3993) = '#skF_4'
      | ~ v1_xboole_0(A_3944) ) ),
    inference(resolution,[status(thm)],[c_73509,c_74402])).

tff(c_75956,plain,(
    ! [A_4086,B_4087,B_4088] :
      ( k3_zfmisc_1(A_4086,B_4087,B_4088) = '#skF_4'
      | ~ v1_xboole_0(A_4086) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_74404])).

tff(c_76279,plain,(
    ! [B_4087,B_4088] : k3_zfmisc_1('#skF_4',B_4087,B_4088) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_73521,c_75956])).

tff(c_73932,plain,(
    ! [B_3967] :
      ( v1_xboole_0(B_3967)
      | B_3967 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73510,c_73306])).

tff(c_72410,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72407,c_82])).

tff(c_73950,plain,(
    k3_zfmisc_1('#skF_4','#skF_8','#skF_9') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_73932,c_72410])).

tff(c_76287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76279,c_73950])).

tff(c_76289,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_73409])).

tff(c_73482,plain,(
    ! [A_3938,B_3939,C_3940,D_3941] :
      ( k5_mcart_1(A_3938,B_3939,C_3940,D_3941) = k1_mcart_1(k1_mcart_1(D_3941))
      | ~ m1_subset_1(D_3941,k3_zfmisc_1(A_3938,B_3939,C_3940))
      | k1_xboole_0 = C_3940
      | k1_xboole_0 = B_3939
      | k1_xboole_0 = A_3938 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_73486,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_72424,c_73482])).

tff(c_76290,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_73486])).

tff(c_76291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76289,c_76290])).

tff(c_76292,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9'
    | k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_73486])).

tff(c_76652,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_76292])).

tff(c_72411,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72407,c_64])).

tff(c_72699,plain,(
    ! [A_3880,B_3881,C_3882] :
      ( r2_hidden(k1_mcart_1(A_3880),B_3881)
      | ~ r2_hidden(A_3880,k2_zfmisc_1(B_3881,C_3882)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_84820,plain,(
    ! [A_4517,A_4518,B_4519,C_4520] :
      ( r2_hidden(k1_mcart_1(A_4517),k2_zfmisc_1(A_4518,B_4519))
      | ~ r2_hidden(A_4517,k3_zfmisc_1(A_4518,B_4519,C_4520)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_72699])).

tff(c_84863,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_72411,c_84820])).

tff(c_84882,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_84863,c_54])).

tff(c_84900,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76652,c_84882])).

tff(c_84902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72429,c_84900])).

tff(c_84903,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_76292])).

tff(c_84905,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_84903])).

tff(c_85481,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84905,c_73306])).

tff(c_87357,plain,(
    ! [B_4641,C_4642] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_4641,C_4642))),B_4641)
      | v1_xboole_0(k2_zfmisc_1(B_4641,C_4642)) ) ),
    inference(resolution,[status(thm)],[c_4,c_72699])).

tff(c_73370,plain,(
    ! [C_3921,B_3922,A_3923] :
      ( v1_xboole_0(C_3921)
      | ~ m1_subset_1(C_3921,k1_zfmisc_1(k2_zfmisc_1(B_3922,A_3923)))
      | ~ v1_xboole_0(A_3923) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_73377,plain,(
    ! [A_32,A_3923,B_3922] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_3923)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_3922,A_3923)) ) ),
    inference(resolution,[status(thm)],[c_40,c_73370])).

tff(c_73384,plain,(
    ! [A_3923,A_32,B_3922] :
      ( ~ v1_xboole_0(A_3923)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_3922,A_3923)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_73377])).

tff(c_87374,plain,(
    ! [A_3923,B_3922,C_4642] :
      ( ~ v1_xboole_0(A_3923)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_3922,A_3923),C_4642)) ) ),
    inference(resolution,[status(thm)],[c_87357,c_73384])).

tff(c_87462,plain,(
    ! [A_4645,B_4646,C_4647] :
      ( ~ v1_xboole_0(A_4645)
      | v1_xboole_0(k3_zfmisc_1(B_4646,A_4645,C_4647)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_87374])).

tff(c_87484,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_87462,c_72410])).

tff(c_87497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85481,c_87484])).

tff(c_87498,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_84903])).

tff(c_72794,plain,(
    ! [B_3894,A_3895] : k3_xboole_0(B_3894,k4_xboole_0(A_3895,B_3894)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_72749])).

tff(c_72808,plain,(
    ! [B_3894,A_3895,C_16] :
      ( ~ r1_xboole_0(B_3894,k4_xboole_0(A_3895,B_3894))
      | ~ r2_hidden(C_16,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72794,c_16])).

tff(c_72823,plain,(
    ! [C_16] : ~ r2_hidden(C_16,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_72808])).

tff(c_87526,plain,(
    ! [C_16] : ~ r2_hidden(C_16,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87498,c_72823])).

tff(c_73019,plain,(
    ! [A_3905,C_3906,B_3907] :
      ( r2_hidden(k2_mcart_1(A_3905),C_3906)
      | ~ r2_hidden(A_3905,k2_zfmisc_1(B_3907,C_3906)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_89005,plain,(
    ! [A_4722,C_4723,A_4724,B_4725] :
      ( r2_hidden(k2_mcart_1(A_4722),C_4723)
      | ~ r2_hidden(A_4722,k3_zfmisc_1(A_4724,B_4725,C_4723)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_73019])).

tff(c_89013,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_72411,c_89005])).

tff(c_89022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87526,c_89013])).

tff(c_89023,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8')
    | ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_89104,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_89023])).

tff(c_90335,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90314,c_89104])).

tff(c_89295,plain,(
    ! [A_4766,C_4767,B_4768] :
      ( r2_hidden(k2_mcart_1(A_4766),C_4767)
      | ~ r2_hidden(A_4766,k2_zfmisc_1(B_4768,C_4767)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_93543,plain,(
    ! [A_5026,C_5027,A_5028,B_5029] :
      ( r2_hidden(k2_mcart_1(A_5026),C_5027)
      | ~ r2_hidden(A_5026,k3_zfmisc_1(A_5028,B_5029,C_5027)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_89295])).

tff(c_93566,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_93543])).

tff(c_93575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90335,c_93566])).

tff(c_93576,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_89123])).

tff(c_93581,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93576,c_66])).

tff(c_95313,plain,(
    ! [A_5163,B_5164,C_5165,D_5166] :
      ( k7_mcart_1(A_5163,B_5164,C_5165,D_5166) = k2_mcart_1(D_5166)
      | ~ m1_subset_1(D_5166,k3_zfmisc_1(A_5163,B_5164,C_5165))
      | k1_xboole_0 = C_5165
      | k1_xboole_0 = B_5164
      | k1_xboole_0 = A_5163 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_95316,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_93581,c_95313])).

tff(c_95319,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_94332,c_94333,c_95316])).

tff(c_95380,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_95319])).

tff(c_94247,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k1_xboole_0 != B_30 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94225,c_93604])).

tff(c_95760,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95380,c_94247])).

tff(c_94433,plain,(
    ! [A_5085,B_5086,C_5087] :
      ( r2_hidden(k1_mcart_1(A_5085),B_5086)
      | ~ r2_hidden(A_5085,k2_zfmisc_1(B_5086,C_5087)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_98333,plain,(
    ! [B_5305,C_5306] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_5305,C_5306))),B_5305)
      | v1_xboole_0(k2_zfmisc_1(B_5305,C_5306)) ) ),
    inference(resolution,[status(thm)],[c_4,c_94433])).

tff(c_94579,plain,(
    ! [C_5101,B_5102,A_5103] :
      ( v1_xboole_0(C_5101)
      | ~ m1_subset_1(C_5101,k1_zfmisc_1(k2_zfmisc_1(B_5102,A_5103)))
      | ~ v1_xboole_0(A_5103) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_94586,plain,(
    ! [A_32,A_5103,B_5102] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_5103)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_5102,A_5103)) ) ),
    inference(resolution,[status(thm)],[c_40,c_94579])).

tff(c_94593,plain,(
    ! [A_5103,A_32,B_5102] :
      ( ~ v1_xboole_0(A_5103)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_5102,A_5103)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_94586])).

tff(c_98354,plain,(
    ! [A_5103,B_5102,C_5306] :
      ( ~ v1_xboole_0(A_5103)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_5102,A_5103),C_5306)) ) ),
    inference(resolution,[status(thm)],[c_98333,c_94593])).

tff(c_98465,plain,(
    ! [A_5312,B_5313,C_5314] :
      ( ~ v1_xboole_0(A_5312)
      | v1_xboole_0(k3_zfmisc_1(B_5313,A_5312,C_5314)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_98354])).

tff(c_98485,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_98465,c_82])).

tff(c_98497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95760,c_98485])).

tff(c_98498,plain,(
    k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_95319])).

tff(c_93578,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93576,c_89104])).

tff(c_98784,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98498,c_93578])).

tff(c_94338,plain,(
    ! [A_5078,B_5079,C_5080] : k2_zfmisc_1(k2_zfmisc_1(A_5078,B_5079),C_5080) = k3_zfmisc_1(A_5078,B_5079,C_5080) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_52,plain,(
    ! [A_47,C_49,B_48] :
      ( r2_hidden(k2_mcart_1(A_47),C_49)
      | ~ r2_hidden(A_47,k2_zfmisc_1(B_48,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_102231,plain,(
    ! [A_5486,C_5487,A_5488,B_5489] :
      ( r2_hidden(k2_mcart_1(A_5486),C_5487)
      | ~ r2_hidden(A_5486,k3_zfmisc_1(A_5488,B_5489,C_5487)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94338,c_52])).

tff(c_102254,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_102231])).

tff(c_102263,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98784,c_102254])).

tff(c_102264,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_89122])).

tff(c_89024,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_89064,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_89024,c_2])).

tff(c_102266,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102264,c_89064])).

tff(c_108438,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_108418,c_102266])).

tff(c_108439,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_108418,c_89197])).

tff(c_102516,plain,(
    ! [A_5518,B_5519] :
      ( k3_xboole_0(A_5518,B_5519) = k1_xboole_0
      | ~ r1_xboole_0(A_5518,B_5519) ) ),
    inference(resolution,[status(thm)],[c_89102,c_89153])).

tff(c_102543,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_102516])).

tff(c_102366,plain,(
    ! [A_5500,B_5501] : r1_xboole_0(k3_xboole_0(A_5500,B_5501),k4_xboole_0(A_5500,B_5501)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89159,c_32])).

tff(c_102383,plain,(
    ! [B_28,A_27] : r1_xboole_0(k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)),B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_102366])).

tff(c_102577,plain,(
    ! [B_5522] : r1_xboole_0(k1_xboole_0,B_5522) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102543,c_102383])).

tff(c_102628,plain,(
    ! [B_5524] : r1_xboole_0(B_5524,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_102577,c_12])).

tff(c_102647,plain,(
    ! [B_5524] : k3_xboole_0(B_5524,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102628,c_89157])).

tff(c_102748,plain,(
    ! [B_5531] : k4_xboole_0(k1_xboole_0,B_5531) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102577,c_34])).

tff(c_102855,plain,(
    ! [B_5533] : k4_xboole_0(B_5533,k1_xboole_0) = B_5533 ),
    inference(superposition,[status(thm),theory(equality)],[c_102748,c_104])).

tff(c_102880,plain,(
    ! [B_5533] : k4_xboole_0(B_5533,B_5533) = k3_xboole_0(B_5533,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_102855,c_26])).

tff(c_102906,plain,(
    ! [B_5533] : k4_xboole_0(B_5533,B_5533) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102647,c_102880])).

tff(c_102306,plain,(
    ! [A_5492] :
      ( ~ r1_xboole_0(A_5492,A_5492)
      | v1_xboole_0(A_5492) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89198,c_89102])).

tff(c_102315,plain,(
    ! [A_4730] :
      ( v1_xboole_0(A_4730)
      | k4_xboole_0(A_4730,A_4730) != A_4730 ) ),
    inference(resolution,[status(thm)],[c_89060,c_102306])).

tff(c_103002,plain,(
    ! [A_5538] :
      ( v1_xboole_0(A_5538)
      | k1_xboole_0 != A_5538 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102906,c_102315])).

tff(c_103026,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_103002,c_102266])).

tff(c_102284,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_89123])).

tff(c_102288,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_89090,c_102284])).

tff(c_103025,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_103002,c_102288])).

tff(c_103027,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_103002,c_89197])).

tff(c_103778,plain,(
    ! [A_5605,B_5606,C_5607,D_5608] :
      ( k7_mcart_1(A_5605,B_5606,C_5607,D_5608) = k2_mcart_1(D_5608)
      | ~ m1_subset_1(D_5608,k3_zfmisc_1(A_5605,B_5606,C_5607))
      | k1_xboole_0 = C_5607
      | k1_xboole_0 = B_5606
      | k1_xboole_0 = A_5605 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_103781,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_103778])).

tff(c_103784,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_103026,c_103025,c_103027,c_103781])).

tff(c_103785,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103784,c_89104])).

tff(c_102270,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102264,c_64])).

tff(c_102675,plain,(
    ! [A_5526,C_5527,B_5528] :
      ( r2_hidden(k2_mcart_1(A_5526),C_5527)
      | ~ r2_hidden(A_5526,k2_zfmisc_1(B_5528,C_5527)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_107620,plain,(
    ! [A_5796,C_5797,A_5798,B_5799] :
      ( r2_hidden(k2_mcart_1(A_5796),C_5797)
      | ~ r2_hidden(A_5796,k3_zfmisc_1(A_5798,B_5799,C_5797)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_102675])).

tff(c_107637,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_102270,c_107620])).

tff(c_107650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103785,c_107637])).

tff(c_107651,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_89123])).

tff(c_107655,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107651,c_66])).

tff(c_109176,plain,(
    ! [A_5918,B_5919,C_5920,D_5921] :
      ( k7_mcart_1(A_5918,B_5919,C_5920,D_5921) = k2_mcart_1(D_5921)
      | ~ m1_subset_1(D_5921,k3_zfmisc_1(A_5918,B_5919,C_5920))
      | k1_xboole_0 = C_5920
      | k1_xboole_0 = B_5919
      | k1_xboole_0 = A_5918 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_109179,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_107655,c_109176])).

tff(c_109182,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_108438,c_108439,c_109179])).

tff(c_109215,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_109182])).

tff(c_108332,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k1_xboole_0 != B_30 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108258,c_107678])).

tff(c_109739,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109215,c_108332])).

tff(c_108318,plain,(
    ! [A_5846,B_5847,C_5848] :
      ( r2_hidden(k1_mcart_1(A_5846),B_5847)
      | ~ r2_hidden(A_5846,k2_zfmisc_1(B_5847,C_5848)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_112351,plain,(
    ! [B_6089,C_6090] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_6089,C_6090))),B_6089)
      | v1_xboole_0(k2_zfmisc_1(B_6089,C_6090)) ) ),
    inference(resolution,[status(thm)],[c_4,c_108318])).

tff(c_108756,plain,(
    ! [C_5876,B_5877,A_5878] :
      ( v1_xboole_0(C_5876)
      | ~ m1_subset_1(C_5876,k1_zfmisc_1(k2_zfmisc_1(B_5877,A_5878)))
      | ~ v1_xboole_0(A_5878) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_108763,plain,(
    ! [A_32,A_5878,B_5877] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_5878)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_5877,A_5878)) ) ),
    inference(resolution,[status(thm)],[c_40,c_108756])).

tff(c_108770,plain,(
    ! [A_5878,A_32,B_5877] :
      ( ~ v1_xboole_0(A_5878)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_5877,A_5878)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_108763])).

tff(c_112372,plain,(
    ! [A_5878,B_5877,C_6090] :
      ( ~ v1_xboole_0(A_5878)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_5877,A_5878),C_6090)) ) ),
    inference(resolution,[status(thm)],[c_112351,c_108770])).

tff(c_112507,plain,(
    ! [A_6096,B_6097,C_6098] :
      ( ~ v1_xboole_0(A_6096)
      | v1_xboole_0(k3_zfmisc_1(B_6097,A_6096,C_6098)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_112372])).

tff(c_102269,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102264,c_82])).

tff(c_112535,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_112507,c_102269])).

tff(c_112551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109739,c_112535])).

tff(c_112552,plain,(
    k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_109182])).

tff(c_107653,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107651,c_89104])).

tff(c_112554,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112552,c_107653])).

tff(c_108467,plain,(
    ! [A_5855,B_5856,C_5857] : k2_zfmisc_1(k2_zfmisc_1(A_5855,B_5856),C_5857) = k3_zfmisc_1(A_5855,B_5856,C_5857) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_117026,plain,(
    ! [A_6308,C_6309,A_6310,B_6311] :
      ( r2_hidden(k2_mcart_1(A_6308),C_6309)
      | ~ r2_hidden(A_6308,k3_zfmisc_1(A_6310,B_6311,C_6309)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108467,c_52])).

tff(c_117043,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_102270,c_117026])).

tff(c_117056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112554,c_117043])).

tff(c_117057,plain,(
    '#skF_6' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_89124])).

tff(c_117062,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_5','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117057,c_66])).

tff(c_118279,plain,(
    ! [A_6400,B_6401,C_6402,D_6403] :
      ( k7_mcart_1(A_6400,B_6401,C_6402,D_6403) = k2_mcart_1(D_6403)
      | ~ m1_subset_1(D_6403,k3_zfmisc_1(A_6400,B_6401,C_6402))
      | k1_xboole_0 = C_6402
      | k1_xboole_0 = B_6401
      | k1_xboole_0 = A_6400 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_118282,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_117062,c_118279])).

tff(c_118285,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_118051,c_118050,c_118282])).

tff(c_118347,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_118285])).

tff(c_117407,plain,(
    ! [B_6346,A_6347] : k3_xboole_0(B_6346,k4_xboole_0(A_6347,B_6346)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_117372])).

tff(c_117421,plain,(
    ! [B_6346,A_6347,C_16] :
      ( ~ r1_xboole_0(B_6346,k4_xboole_0(A_6347,B_6346))
      | ~ r2_hidden(C_16,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117407,c_16])).

tff(c_117436,plain,(
    ! [C_16] : ~ r2_hidden(C_16,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_117421])).

tff(c_118373,plain,(
    ! [C_16] : ~ r2_hidden(C_16,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118347,c_117436])).

tff(c_117688,plain,(
    ! [A_6360,B_6361,C_6362] : k2_zfmisc_1(k2_zfmisc_1(A_6360,B_6361),C_6362) = k3_zfmisc_1(A_6360,B_6361,C_6362) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_120545,plain,(
    ! [A_6523,C_6524,A_6525,B_6526] :
      ( r2_hidden(k2_mcart_1(A_6523),C_6524)
      | ~ r2_hidden(A_6523,k3_zfmisc_1(A_6525,B_6526,C_6524)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117688,c_52])).

tff(c_120559,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_120545])).

tff(c_120567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118373,c_120559])).

tff(c_120568,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_118285])).

tff(c_117059,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117057,c_89104])).

tff(c_120613,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120568,c_117059])).

tff(c_123487,plain,(
    ! [A_6699,C_6700,A_6701,B_6702] :
      ( r2_hidden(k2_mcart_1(A_6699),C_6700)
      | ~ r2_hidden(A_6699,k3_zfmisc_1(A_6701,B_6702,C_6700)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117688,c_52])).

tff(c_123510,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_123487])).

tff(c_123519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120613,c_123510])).

tff(c_123520,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_89123])).

tff(c_123522,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123520,c_117062])).

tff(c_125163,plain,(
    ! [A_6831,B_6832,C_6833,D_6834] :
      ( k7_mcart_1(A_6831,B_6832,C_6833,D_6834) = k2_mcart_1(D_6834)
      | ~ m1_subset_1(D_6834,k3_zfmisc_1(A_6831,B_6832,C_6833))
      | k1_xboole_0 = C_6833
      | k1_xboole_0 = B_6832
      | k1_xboole_0 = A_6831 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_125166,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_123522,c_125163])).

tff(c_125169,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_124238,c_124713,c_125166])).

tff(c_125201,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_125169])).

tff(c_124504,plain,(
    ! [A_6775,B_6777] :
      ( ~ v1_xboole_0(A_6775)
      | v1_xboole_0(k2_zfmisc_1(B_6777,A_6775)) ) ),
    inference(resolution,[status(thm)],[c_4,c_124491])).

tff(c_124691,plain,(
    ! [C_6793,A_6794,B_6795] :
      ( v1_xboole_0(C_6793)
      | ~ m1_subset_1(C_6793,k1_zfmisc_1(k2_zfmisc_1(A_6794,B_6795)))
      | ~ v1_xboole_0(A_6794) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_124701,plain,(
    ! [A_32,A_6794,B_6795] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_6794)
      | ~ r2_hidden(A_32,k2_zfmisc_1(A_6794,B_6795)) ) ),
    inference(resolution,[status(thm)],[c_40,c_124691])).

tff(c_124714,plain,(
    ! [A_6796,A_6797,B_6798] :
      ( ~ v1_xboole_0(A_6796)
      | ~ r2_hidden(A_6797,k2_zfmisc_1(A_6796,B_6798)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_124701])).

tff(c_124747,plain,(
    ! [A_6801,B_6802] :
      ( ~ v1_xboole_0(A_6801)
      | v1_xboole_0(k2_zfmisc_1(A_6801,B_6802)) ) ),
    inference(resolution,[status(thm)],[c_4,c_124714])).

tff(c_89147,plain,(
    ! [A_4740] :
      ( k1_xboole_0 = A_4740
      | ~ v1_xboole_0(A_4740) ) ),
    inference(resolution,[status(thm)],[c_89090,c_89130])).

tff(c_124768,plain,(
    ! [A_6803,B_6804] :
      ( k2_zfmisc_1(A_6803,B_6804) = k1_xboole_0
      | ~ v1_xboole_0(A_6803) ) ),
    inference(resolution,[status(thm)],[c_124747,c_89147])).

tff(c_124774,plain,(
    ! [B_6777,A_6775,B_6804] :
      ( k2_zfmisc_1(k2_zfmisc_1(B_6777,A_6775),B_6804) = k1_xboole_0
      | ~ v1_xboole_0(A_6775) ) ),
    inference(resolution,[status(thm)],[c_124504,c_124768])).

tff(c_125036,plain,(
    ! [B_6823,A_6824,B_6825] :
      ( k3_zfmisc_1(B_6823,A_6824,B_6825) = k1_xboole_0
      | ~ v1_xboole_0(A_6824) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_124774])).

tff(c_125050,plain,(
    ! [B_6823,B_30,B_6825] :
      ( k3_zfmisc_1(B_6823,B_30,B_6825) = k1_xboole_0
      | k1_xboole_0 != B_30 ) ),
    inference(resolution,[status(thm)],[c_124144,c_125036])).

tff(c_128750,plain,(
    ! [B_6823,B_6825] : k3_zfmisc_1(B_6823,'#skF_8',B_6825) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125201,c_125201,c_125050])).

tff(c_124241,plain,(
    k3_zfmisc_1('#skF_7','#skF_8','#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124219,c_82])).

tff(c_125226,plain,(
    k3_zfmisc_1('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125201,c_124241])).

tff(c_128758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128750,c_125226])).

tff(c_128759,plain,(
    k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_125169])).

tff(c_123749,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123520,c_117059])).

tff(c_128768,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128759,c_123749])).

tff(c_123914,plain,(
    ! [A_6737,C_6738,B_6739] :
      ( r2_hidden(k2_mcart_1(A_6737),C_6738)
      | ~ r2_hidden(A_6737,k2_zfmisc_1(B_6739,C_6738)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_132820,plain,(
    ! [A_7204,C_7205,A_7206,B_7207] :
      ( r2_hidden(k2_mcart_1(A_7204),C_7205)
      | ~ r2_hidden(A_7204,k3_zfmisc_1(A_7206,B_7207,C_7205)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_123914])).

tff(c_132846,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_132820])).

tff(c_132856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128768,c_132846])).

tff(c_132857,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_89122])).

tff(c_132861,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132857,c_82])).

tff(c_144961,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_144939,c_132861])).

tff(c_144973,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(resolution,[status(thm)],[c_140748,c_144961])).

tff(c_140814,plain,(
    ! [A_7676] :
      ( v1_xboole_0(A_7676)
      | k1_xboole_0 != A_7676 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140747,c_140016])).

tff(c_132859,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132857,c_89064])).

tff(c_140831,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_140814,c_132859])).

tff(c_133149,plain,(
    ! [A_7237,B_7238] :
      ( k3_xboole_0(A_7237,B_7238) = k1_xboole_0
      | ~ r1_xboole_0(A_7237,B_7238) ) ),
    inference(resolution,[status(thm)],[c_89102,c_89153])).

tff(c_133180,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_133149])).

tff(c_132892,plain,(
    ! [A_7209,B_7210] : k4_xboole_0(A_7209,k4_xboole_0(A_7209,B_7210)) = k3_xboole_0(A_7209,B_7210) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_132991,plain,(
    ! [A_7218,B_7219] : r1_xboole_0(k3_xboole_0(A_7218,B_7219),k4_xboole_0(A_7218,B_7219)) ),
    inference(superposition,[status(thm),theory(equality)],[c_132892,c_32])).

tff(c_133044,plain,(
    ! [A_7224,B_7225] : r1_xboole_0(k4_xboole_0(A_7224,B_7225),k3_xboole_0(A_7224,B_7225)) ),
    inference(resolution,[status(thm)],[c_132991,c_12])).

tff(c_133061,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_133044])).

tff(c_133283,plain,(
    ! [B_7247] : r1_xboole_0(B_7247,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133180,c_133061])).

tff(c_133306,plain,(
    ! [B_7247] : k3_xboole_0(B_7247,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_133283,c_89157])).

tff(c_133480,plain,(
    ! [B_7257] : k4_xboole_0(B_7257,k1_xboole_0) = B_7257 ),
    inference(resolution,[status(thm)],[c_133283,c_34])).

tff(c_133508,plain,(
    ! [B_7257] : k4_xboole_0(B_7257,B_7257) = k3_xboole_0(B_7257,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_133480,c_26])).

tff(c_133534,plain,(
    ! [B_7257] : k4_xboole_0(B_7257,B_7257) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133306,c_133508])).

tff(c_132927,plain,(
    ! [B_7211] : k3_xboole_0(B_7211,B_7211) = B_7211 ),
    inference(superposition,[status(thm),theory(equality)],[c_132892,c_104])).

tff(c_132943,plain,(
    ! [B_7212] :
      ( ~ r1_xboole_0(B_7212,B_7212)
      | v1_xboole_0(B_7212) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132927,c_89102])).

tff(c_132953,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k4_xboole_0(B_30,B_30) != B_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_132943])).

tff(c_133684,plain,(
    ! [B_7264] :
      ( v1_xboole_0(B_7264)
      | k1_xboole_0 != B_7264 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133534,c_132953])).

tff(c_133705,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_133684,c_132859])).

tff(c_132875,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_89123])).

tff(c_132879,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_89090,c_132875])).

tff(c_133704,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_133684,c_132879])).

tff(c_134172,plain,(
    ! [A_7307,B_7308,C_7309,D_7310] :
      ( k7_mcart_1(A_7307,B_7308,C_7309,D_7310) = k2_mcart_1(D_7310)
      | ~ m1_subset_1(D_7310,k3_zfmisc_1(A_7307,B_7308,C_7309))
      | k1_xboole_0 = C_7309
      | k1_xboole_0 = B_7308
      | k1_xboole_0 = A_7307 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_134175,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_117062,c_134172])).

tff(c_134178,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_133705,c_133704,c_134175])).

tff(c_134287,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_134178])).

tff(c_133207,plain,(
    ! [A_7242,B_7243] : k3_xboole_0(k4_xboole_0(A_7242,B_7243),B_7243) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_133149])).

tff(c_133221,plain,(
    ! [A_7242,B_7243,C_16] :
      ( ~ r1_xboole_0(k4_xboole_0(A_7242,B_7243),B_7243)
      | ~ r2_hidden(C_16,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133207,c_16])).

tff(c_133234,plain,(
    ! [C_16] : ~ r2_hidden(C_16,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_133221])).

tff(c_134316,plain,(
    ! [C_16] : ~ r2_hidden(C_16,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134287,c_133234])).

tff(c_132862,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132857,c_64])).

tff(c_133345,plain,(
    ! [A_7249,C_7250,B_7251] :
      ( r2_hidden(k2_mcart_1(A_7249),C_7250)
      | ~ r2_hidden(A_7249,k2_zfmisc_1(B_7251,C_7250)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_136539,plain,(
    ! [A_7428,C_7429,A_7430,B_7431] :
      ( r2_hidden(k2_mcart_1(A_7428),C_7429)
      | ~ r2_hidden(A_7428,k3_zfmisc_1(A_7430,B_7431,C_7429)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_133345])).

tff(c_136547,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_132862,c_136539])).

tff(c_136559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134316,c_136547])).

tff(c_136560,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_134178])).

tff(c_136629,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136560,c_117059])).

tff(c_139886,plain,(
    ! [A_7615,C_7616,A_7617,B_7618] :
      ( r2_hidden(k2_mcart_1(A_7615),C_7616)
      | ~ r2_hidden(A_7615,k3_zfmisc_1(A_7617,B_7618,C_7616)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_133345])).

tff(c_139900,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_132862,c_139886])).

tff(c_139912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136629,c_139900])).

tff(c_139913,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_89123])).

tff(c_139915,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139913,c_117062])).

tff(c_141730,plain,(
    ! [A_7738,B_7739,C_7740,D_7741] :
      ( k7_mcart_1(A_7738,B_7739,C_7740,D_7741) = k2_mcart_1(D_7741)
      | ~ m1_subset_1(D_7741,k3_zfmisc_1(A_7738,B_7739,C_7740))
      | k1_xboole_0 = C_7740
      | k1_xboole_0 = B_7739
      | k1_xboole_0 = A_7738 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_141733,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_139915,c_141730])).

tff(c_141736,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_140831,c_141733])).

tff(c_141822,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_141736])).

tff(c_141935,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141822,c_140748])).

tff(c_140451,plain,(
    ! [A_7655,B_7656,C_7657] :
      ( r2_hidden(k1_mcart_1(A_7655),B_7656)
      | ~ r2_hidden(A_7655,k2_zfmisc_1(B_7656,C_7657)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_144603,plain,(
    ! [B_7899,C_7900] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_7899,C_7900))),B_7899)
      | v1_xboole_0(k2_zfmisc_1(B_7899,C_7900)) ) ),
    inference(resolution,[status(thm)],[c_4,c_140451])).

tff(c_141530,plain,(
    ! [A_7724,A_32,B_7723] :
      ( ~ v1_xboole_0(A_7724)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_7723,A_7724)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_141523])).

tff(c_144624,plain,(
    ! [A_7724,B_7723,C_7900] :
      ( ~ v1_xboole_0(A_7724)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_7723,A_7724),C_7900)) ) ),
    inference(resolution,[status(thm)],[c_144603,c_141530])).

tff(c_144741,plain,(
    ! [A_7906,B_7907,C_7908] :
      ( ~ v1_xboole_0(A_7906)
      | v1_xboole_0(k3_zfmisc_1(B_7907,A_7906,C_7908)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_144624])).

tff(c_144763,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_144741,c_132861])).

tff(c_144776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141935,c_144763])).

tff(c_144777,plain,
    ( k1_xboole_0 = '#skF_9'
    | k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_141736])).

tff(c_145442,plain,(
    k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_144973,c_144777])).

tff(c_140117,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139913,c_117059])).

tff(c_145443,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145442,c_140117])).

tff(c_140898,plain,(
    ! [A_7683,B_7684,C_7685] : k2_zfmisc_1(k2_zfmisc_1(A_7683,B_7684),C_7685) = k3_zfmisc_1(A_7683,B_7684,C_7685) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_148839,plain,(
    ! [A_8123,C_8124,A_8125,B_8126] :
      ( r2_hidden(k2_mcart_1(A_8123),C_8124)
      | ~ r2_hidden(A_8123,k3_zfmisc_1(A_8125,B_8126,C_8124)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_140898,c_52])).

tff(c_148856,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_132862,c_148839])).

tff(c_148869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145443,c_148856])).

tff(c_148870,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_89023])).

tff(c_148968,plain,(
    ! [B_8136,A_8137] :
      ( B_8136 = A_8137
      | ~ r1_tarski(B_8136,A_8137)
      | ~ r1_tarski(A_8137,B_8136) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_148994,plain,(
    ! [A_8138] :
      ( k1_xboole_0 = A_8138
      | ~ r1_tarski(A_8138,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_148968])).

tff(c_149017,plain,(
    ! [A_8139] :
      ( k1_xboole_0 = A_8139
      | ~ v1_xboole_0(A_8139) ) ),
    inference(resolution,[status(thm)],[c_89090,c_148994])).

tff(c_184310,plain,(
    ! [A_9905,B_9906] :
      ( k3_xboole_0(A_9905,B_9906) = k1_xboole_0
      | ~ r1_xboole_0(A_9905,B_9906) ) ),
    inference(resolution,[status(thm)],[c_89102,c_149017])).

tff(c_184335,plain,(
    ! [B_9907,A_9908] : k3_xboole_0(B_9907,k4_xboole_0(A_9908,B_9907)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_184310])).

tff(c_148915,plain,(
    ! [A_8133,B_8134] : k4_xboole_0(A_8133,k4_xboole_0(A_8133,B_8134)) = k3_xboole_0(A_8133,B_8134) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_148934,plain,(
    ! [A_8133,B_8134] : r1_xboole_0(k4_xboole_0(A_8133,B_8134),k3_xboole_0(A_8133,B_8134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148915,c_91])).

tff(c_184340,plain,(
    ! [B_9907,A_9908] : r1_xboole_0(k4_xboole_0(B_9907,k4_xboole_0(A_9908,B_9907)),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_184335,c_148934])).

tff(c_184366,plain,(
    ! [B_9909] : r1_xboole_0(B_9909,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_184340])).

tff(c_149026,plain,(
    ! [A_4744,B_4745] :
      ( k3_xboole_0(A_4744,B_4745) = k1_xboole_0
      | ~ r1_xboole_0(A_4744,B_4745) ) ),
    inference(resolution,[status(thm)],[c_89102,c_149017])).

tff(c_184385,plain,(
    ! [B_9909] : k3_xboole_0(B_9909,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_184366,c_149026])).

tff(c_184472,plain,(
    ! [B_9918] : k4_xboole_0(B_9918,k1_xboole_0) = B_9918 ),
    inference(resolution,[status(thm)],[c_184366,c_34])).

tff(c_184490,plain,(
    ! [B_9918] : k4_xboole_0(B_9918,B_9918) = k3_xboole_0(B_9918,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_184472,c_26])).

tff(c_184911,plain,(
    ! [B_9918] : k4_xboole_0(B_9918,B_9918) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_184385,c_184490])).

tff(c_148953,plain,(
    ! [B_8135] : k3_xboole_0(B_8135,B_8135) = B_8135 ),
    inference(superposition,[status(thm),theory(equality)],[c_148915,c_104])).

tff(c_184182,plain,(
    ! [B_9889] :
      ( ~ r1_xboole_0(B_9889,B_9889)
      | v1_xboole_0(B_9889) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148953,c_89102])).

tff(c_184191,plain,(
    ! [A_4730] :
      ( v1_xboole_0(A_4730)
      | k4_xboole_0(A_4730,A_4730) != A_4730 ) ),
    inference(resolution,[status(thm)],[c_89060,c_184182])).

tff(c_184978,plain,(
    ! [A_9939] :
      ( v1_xboole_0(A_9939)
      | k1_xboole_0 != A_9939 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184911,c_184191])).

tff(c_149258,plain,(
    ! [A_8167,B_8168] :
      ( k3_xboole_0(A_8167,B_8168) = k1_xboole_0
      | ~ r1_xboole_0(A_8167,B_8168) ) ),
    inference(resolution,[status(thm)],[c_89102,c_149017])).

tff(c_149289,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_149258])).

tff(c_149139,plain,(
    ! [A_8156,B_8157] : r1_xboole_0(k4_xboole_0(A_8156,B_8157),k3_xboole_0(A_8156,B_8157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148915,c_91])).

tff(c_149158,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_149139])).

tff(c_149364,plain,(
    ! [B_8175] : r1_xboole_0(B_8175,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149289,c_149158])).

tff(c_149385,plain,(
    ! [B_8175] : k3_xboole_0(B_8175,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149364,c_149026])).

tff(c_149547,plain,(
    ! [B_8183] : k4_xboole_0(B_8183,k1_xboole_0) = B_8183 ),
    inference(resolution,[status(thm)],[c_149364,c_34])).

tff(c_149569,plain,(
    ! [B_8183] : k4_xboole_0(B_8183,B_8183) = k3_xboole_0(B_8183,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_149547,c_26])).

tff(c_149931,plain,(
    ! [B_8183] : k4_xboole_0(B_8183,B_8183) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149385,c_149569])).

tff(c_149067,plain,(
    ! [B_8146] :
      ( ~ r1_xboole_0(B_8146,B_8146)
      | v1_xboole_0(B_8146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148953,c_89102])).

tff(c_149076,plain,(
    ! [A_4730] :
      ( v1_xboole_0(A_4730)
      | k4_xboole_0(A_4730,A_4730) != A_4730 ) ),
    inference(resolution,[status(thm)],[c_89060,c_149067])).

tff(c_149998,plain,(
    ! [A_8203] :
      ( v1_xboole_0(A_8203)
      | k1_xboole_0 != A_8203 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149931,c_149076])).

tff(c_148985,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_118,c_148968])).

tff(c_149027,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_148985])).

tff(c_149031,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_89090,c_149027])).

tff(c_150028,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_149998,c_149031])).

tff(c_148986,plain,
    ( '#skF_5' = '#skF_8'
    | ~ r1_tarski('#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_117,c_148968])).

tff(c_149032,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_148986])).

tff(c_149036,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_89090,c_149032])).

tff(c_150027,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_149998,c_149036])).

tff(c_148987,plain,
    ( '#skF_6' = '#skF_9'
    | ~ r1_tarski('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_116,c_148968])).

tff(c_149046,plain,(
    ~ r1_tarski('#skF_6','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_148987])).

tff(c_149050,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_89090,c_149046])).

tff(c_150026,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_149998,c_149050])).

tff(c_150380,plain,(
    ! [A_8243,B_8244,C_8245,D_8246] :
      ( k6_mcart_1(A_8243,B_8244,C_8245,D_8246) = k2_mcart_1(k1_mcart_1(D_8246))
      | ~ m1_subset_1(D_8246,k3_zfmisc_1(A_8243,B_8244,C_8245))
      | k1_xboole_0 = C_8245
      | k1_xboole_0 = B_8244
      | k1_xboole_0 = A_8243 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_150383,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_150380])).

tff(c_150386,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_150028,c_150027,c_150026,c_150383])).

tff(c_149446,plain,(
    ! [A_8178,B_8179,C_8180] : k2_zfmisc_1(k2_zfmisc_1(A_8178,B_8179),C_8180) = k3_zfmisc_1(A_8178,B_8179,C_8180) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_155270,plain,(
    ! [A_8458,A_8459,B_8460,C_8461] :
      ( r2_hidden(k1_mcart_1(A_8458),k2_zfmisc_1(A_8459,B_8460))
      | ~ r2_hidden(A_8458,k3_zfmisc_1(A_8459,B_8460,C_8461)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149446,c_54])).

tff(c_155314,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_155270])).

tff(c_155382,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_155314,c_52])).

tff(c_155401,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150386,c_155382])).

tff(c_155403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148870,c_155401])).

tff(c_155404,plain,(
    '#skF_6' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_148987])).

tff(c_155407,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155404,c_148870])).

tff(c_155589,plain,(
    ! [A_8483,B_8484] :
      ( k3_xboole_0(A_8483,B_8484) = k1_xboole_0
      | ~ r1_xboole_0(A_8483,B_8484) ) ),
    inference(resolution,[status(thm)],[c_89102,c_149017])).

tff(c_155614,plain,(
    ! [B_8485,A_8486] : k3_xboole_0(B_8485,k4_xboole_0(A_8486,B_8485)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_155589])).

tff(c_155619,plain,(
    ! [B_8485,A_8486] : r1_xboole_0(k4_xboole_0(B_8485,k4_xboole_0(A_8486,B_8485)),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_155614,c_148934])).

tff(c_155645,plain,(
    ! [B_8487] : r1_xboole_0(B_8487,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_155619])).

tff(c_155664,plain,(
    ! [B_8487] : k3_xboole_0(B_8487,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_155645,c_149026])).

tff(c_155857,plain,(
    ! [B_8496] : k4_xboole_0(B_8496,k1_xboole_0) = B_8496 ),
    inference(resolution,[status(thm)],[c_155645,c_34])).

tff(c_155879,plain,(
    ! [B_8496] : k4_xboole_0(B_8496,B_8496) = k3_xboole_0(B_8496,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_155857,c_26])).

tff(c_155905,plain,(
    ! [B_8496] : k4_xboole_0(B_8496,B_8496) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_155664,c_155879])).

tff(c_155423,plain,(
    ! [B_8463] :
      ( ~ r1_xboole_0(B_8463,B_8463)
      | v1_xboole_0(B_8463) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148953,c_89102])).

tff(c_155433,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k4_xboole_0(B_30,B_30) != B_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_155423])).

tff(c_156073,plain,(
    ! [B_8503] :
      ( v1_xboole_0(B_8503)
      | k1_xboole_0 != B_8503 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155905,c_155433])).

tff(c_156099,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_156073,c_149031])).

tff(c_156098,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_156073,c_149036])).

tff(c_148871,plain,(
    r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_89023])).

tff(c_148875,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_148871,c_2])).

tff(c_156101,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(resolution,[status(thm)],[c_156073,c_148875])).

tff(c_155410,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_5','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155404,c_66])).

tff(c_156857,plain,(
    ! [A_8571,B_8572,C_8573,D_8574] :
      ( k6_mcart_1(A_8571,B_8572,C_8573,D_8574) = k2_mcart_1(k1_mcart_1(D_8574))
      | ~ m1_subset_1(D_8574,k3_zfmisc_1(A_8571,B_8572,C_8573))
      | k1_xboole_0 = C_8573
      | k1_xboole_0 = B_8572
      | k1_xboole_0 = A_8571 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_156860,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_155410,c_156857])).

tff(c_156863,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_156099,c_156098,c_156101,c_156860])).

tff(c_155557,plain,(
    ! [A_8480,B_8481,C_8482] : k2_zfmisc_1(k2_zfmisc_1(A_8480,B_8481),C_8482) = k3_zfmisc_1(A_8480,B_8481,C_8482) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_161337,plain,(
    ! [A_8763,A_8764,B_8765,C_8766] :
      ( r2_hidden(k1_mcart_1(A_8763),k2_zfmisc_1(A_8764,B_8765))
      | ~ r2_hidden(A_8763,k3_zfmisc_1(A_8764,B_8765,C_8766)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155557,c_54])).

tff(c_161382,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_161337])).

tff(c_161396,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_161382,c_52])).

tff(c_161415,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156863,c_161396])).

tff(c_161417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155407,c_161415])).

tff(c_161418,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_148986])).

tff(c_161421,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161418,c_148870])).

tff(c_161629,plain,(
    ! [A_8791,B_8792] :
      ( k3_xboole_0(A_8791,B_8792) = k1_xboole_0
      | ~ r1_xboole_0(A_8791,B_8792) ) ),
    inference(resolution,[status(thm)],[c_89102,c_149017])).

tff(c_161656,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_161629])).

tff(c_161550,plain,(
    ! [A_8781,B_8782] : r1_xboole_0(k4_xboole_0(A_8781,B_8782),k3_xboole_0(A_8781,B_8782)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148915,c_91])).

tff(c_161567,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_161550])).

tff(c_161690,plain,(
    ! [B_8795] : r1_xboole_0(B_8795,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161656,c_161567])).

tff(c_161711,plain,(
    ! [B_8795] : k3_xboole_0(B_8795,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_161690,c_149026])).

tff(c_161795,plain,(
    ! [B_8802] : k4_xboole_0(B_8802,k1_xboole_0) = B_8802 ),
    inference(resolution,[status(thm)],[c_161690,c_34])).

tff(c_161813,plain,(
    ! [B_8802] : k4_xboole_0(B_8802,B_8802) = k3_xboole_0(B_8802,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_161795,c_26])).

tff(c_162203,plain,(
    ! [B_8802] : k4_xboole_0(B_8802,B_8802) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_161711,c_161813])).

tff(c_161442,plain,(
    ! [B_8767] :
      ( ~ r1_xboole_0(B_8767,B_8767)
      | v1_xboole_0(B_8767) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148953,c_89102])).

tff(c_161452,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k4_xboole_0(B_30,B_30) != B_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_161442])).

tff(c_162305,plain,(
    ! [B_8823] :
      ( v1_xboole_0(B_8823)
      | k1_xboole_0 != B_8823 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162203,c_161452])).

tff(c_162331,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_162305,c_149031])).

tff(c_161437,plain,(
    ~ r1_tarski('#skF_6','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_148987])).

tff(c_161441,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_89090,c_161437])).

tff(c_162330,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_162305,c_161441])).

tff(c_161424,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161418,c_66])).

tff(c_162505,plain,(
    ! [A_8841,B_8842,C_8843,D_8844] :
      ( k7_mcart_1(A_8841,B_8842,C_8843,D_8844) = k2_mcart_1(D_8844)
      | ~ m1_subset_1(D_8844,k3_zfmisc_1(A_8841,B_8842,C_8843))
      | k1_xboole_0 = C_8843
      | k1_xboole_0 = B_8842
      | k1_xboole_0 = A_8841 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_162508,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_161424,c_162505])).

tff(c_162511,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_162331,c_162330,c_162508])).

tff(c_162578,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_162511])).

tff(c_162204,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k1_xboole_0 != B_30 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162203,c_161452])).

tff(c_163064,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162578,c_162204])).

tff(c_161946,plain,(
    ! [A_8805,B_8806,C_8807] :
      ( r2_hidden(k1_mcart_1(A_8805),B_8806)
      | ~ r2_hidden(A_8805,k2_zfmisc_1(B_8806,C_8807)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_165883,plain,(
    ! [B_9019,C_9020] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_9019,C_9020))),B_9019)
      | v1_xboole_0(k2_zfmisc_1(B_9019,C_9020)) ) ),
    inference(resolution,[status(thm)],[c_4,c_161946])).

tff(c_162379,plain,(
    ! [C_8829,B_8830,A_8831] :
      ( v1_xboole_0(C_8829)
      | ~ m1_subset_1(C_8829,k1_zfmisc_1(k2_zfmisc_1(B_8830,A_8831)))
      | ~ v1_xboole_0(A_8831) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_162386,plain,(
    ! [A_32,A_8831,B_8830] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_8831)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_8830,A_8831)) ) ),
    inference(resolution,[status(thm)],[c_40,c_162379])).

tff(c_162393,plain,(
    ! [A_8831,A_32,B_8830] :
      ( ~ v1_xboole_0(A_8831)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_8830,A_8831)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_162386])).

tff(c_165900,plain,(
    ! [A_8831,B_8830,C_9020] :
      ( ~ v1_xboole_0(A_8831)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_8830,A_8831),C_9020)) ) ),
    inference(resolution,[status(thm)],[c_165883,c_162393])).

tff(c_166021,plain,(
    ! [A_9026,B_9027,C_9028] :
      ( ~ v1_xboole_0(A_9026)
      | v1_xboole_0(k3_zfmisc_1(B_9027,A_9026,C_9028)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_165900])).

tff(c_166043,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_166021,c_82])).

tff(c_166056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_163064,c_166043])).

tff(c_166058,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_162511])).

tff(c_166161,plain,(
    ! [A_9041,B_9042,C_9043,D_9044] :
      ( k6_mcart_1(A_9041,B_9042,C_9043,D_9044) = k2_mcart_1(k1_mcart_1(D_9044))
      | ~ m1_subset_1(D_9044,k3_zfmisc_1(A_9041,B_9042,C_9043))
      | k1_xboole_0 = C_9043
      | k1_xboole_0 = B_9042
      | k1_xboole_0 = A_9041 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_166164,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_161424,c_166161])).

tff(c_166167,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_162331,c_166058,c_162330,c_166164])).

tff(c_171941,plain,(
    ! [A_9297,A_9298,B_9299,C_9300] :
      ( r2_hidden(k1_mcart_1(A_9297),k2_zfmisc_1(A_9298,B_9299))
      | ~ r2_hidden(A_9297,k3_zfmisc_1(A_9298,B_9299,C_9300)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_161946])).

tff(c_171989,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_171941])).

tff(c_172018,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_171989,c_52])).

tff(c_172036,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166167,c_172018])).

tff(c_172038,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161421,c_172036])).

tff(c_172039,plain,(
    '#skF_6' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_148987])).

tff(c_172178,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172039,c_161421])).

tff(c_172219,plain,(
    ! [A_9322,B_9323] :
      ( k3_xboole_0(A_9322,B_9323) = k1_xboole_0
      | ~ r1_xboole_0(A_9322,B_9323) ) ),
    inference(resolution,[status(thm)],[c_89102,c_149017])).

tff(c_172246,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_172219])).

tff(c_172098,plain,(
    ! [A_9309,B_9310] : r1_xboole_0(k3_xboole_0(A_9309,B_9310),k4_xboole_0(A_9309,B_9310)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148915,c_32])).

tff(c_172154,plain,(
    ! [A_9315,B_9316] : r1_xboole_0(k4_xboole_0(A_9315,B_9316),k3_xboole_0(A_9315,B_9316)) ),
    inference(resolution,[status(thm)],[c_172098,c_12])).

tff(c_172171,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_172154])).

tff(c_172345,plain,(
    ! [B_9332] : r1_xboole_0(B_9332,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172246,c_172171])).

tff(c_172368,plain,(
    ! [B_9332] : k3_xboole_0(B_9332,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_172345,c_149026])).

tff(c_172480,plain,(
    ! [B_9339] : k4_xboole_0(B_9339,k1_xboole_0) = B_9339 ),
    inference(resolution,[status(thm)],[c_172345,c_34])).

tff(c_172501,plain,(
    ! [B_9339] : k4_xboole_0(B_9339,B_9339) = k3_xboole_0(B_9339,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_172480,c_26])).

tff(c_172523,plain,(
    ! [B_9339] : k4_xboole_0(B_9339,B_9339) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172368,c_172501])).

tff(c_172054,plain,(
    ! [B_9301] :
      ( ~ r1_xboole_0(B_9301,B_9301)
      | v1_xboole_0(B_9301) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148953,c_89102])).

tff(c_172063,plain,(
    ! [A_4730] :
      ( v1_xboole_0(A_4730)
      | k4_xboole_0(A_4730,A_4730) != A_4730 ) ),
    inference(resolution,[status(thm)],[c_89060,c_172054])).

tff(c_172736,plain,(
    ! [A_9346] :
      ( v1_xboole_0(A_9346)
      | k1_xboole_0 != A_9346 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172523,c_172063])).

tff(c_172758,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_172736,c_149031])).

tff(c_172760,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(resolution,[status(thm)],[c_172736,c_148875])).

tff(c_172078,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172039,c_161424])).

tff(c_173258,plain,(
    ! [A_9392,B_9393,C_9394,D_9395] :
      ( k7_mcart_1(A_9392,B_9393,C_9394,D_9395) = k2_mcart_1(D_9395)
      | ~ m1_subset_1(D_9395,k3_zfmisc_1(A_9392,B_9393,C_9394))
      | k1_xboole_0 = C_9394
      | k1_xboole_0 = B_9393
      | k1_xboole_0 = A_9392 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_173261,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_172078,c_173258])).

tff(c_173264,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_172758,c_172760,c_173261])).

tff(c_173369,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_173264])).

tff(c_172658,plain,(
    ! [A_4730] :
      ( v1_xboole_0(A_4730)
      | k1_xboole_0 != A_4730 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172523,c_172063])).

tff(c_173715,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173369,c_172658])).

tff(c_172088,plain,(
    ! [A_9305,B_9306,C_9307] :
      ( r2_hidden(k1_mcart_1(A_9305),B_9306)
      | ~ r2_hidden(A_9305,k2_zfmisc_1(B_9306,C_9307)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_176771,plain,(
    ! [B_9574,C_9575] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_9574,C_9575))),B_9574)
      | v1_xboole_0(k2_zfmisc_1(B_9574,C_9575)) ) ),
    inference(resolution,[status(thm)],[c_4,c_172088])).

tff(c_172860,plain,(
    ! [C_9354,B_9355,A_9356] :
      ( v1_xboole_0(C_9354)
      | ~ m1_subset_1(C_9354,k1_zfmisc_1(k2_zfmisc_1(B_9355,A_9356)))
      | ~ v1_xboole_0(A_9356) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_172867,plain,(
    ! [A_32,A_9356,B_9355] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_9356)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_9355,A_9356)) ) ),
    inference(resolution,[status(thm)],[c_40,c_172860])).

tff(c_172874,plain,(
    ! [A_9356,A_32,B_9355] :
      ( ~ v1_xboole_0(A_9356)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_9355,A_9356)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_172867])).

tff(c_176792,plain,(
    ! [A_9356,B_9355,C_9575] :
      ( ~ v1_xboole_0(A_9356)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_9355,A_9356),C_9575)) ) ),
    inference(resolution,[status(thm)],[c_176771,c_172874])).

tff(c_176927,plain,(
    ! [A_9581,B_9582,C_9583] :
      ( ~ v1_xboole_0(A_9581)
      | v1_xboole_0(k3_zfmisc_1(B_9582,A_9581,C_9583)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_176792])).

tff(c_176955,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_176927,c_82])).

tff(c_176971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173715,c_176955])).

tff(c_176973,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_173264])).

tff(c_177054,plain,(
    ! [A_9590,B_9591,C_9592,D_9593] :
      ( k6_mcart_1(A_9590,B_9591,C_9592,D_9593) = k2_mcart_1(k1_mcart_1(D_9593))
      | ~ m1_subset_1(D_9593,k3_zfmisc_1(A_9590,B_9591,C_9592))
      | k1_xboole_0 = C_9592
      | k1_xboole_0 = B_9591
      | k1_xboole_0 = A_9590 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_177057,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_172078,c_177054])).

tff(c_177060,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_172758,c_176973,c_172760,c_177057])).

tff(c_172179,plain,(
    ! [A_9317,B_9318,C_9319] : k2_zfmisc_1(k2_zfmisc_1(A_9317,B_9318),C_9319) = k3_zfmisc_1(A_9317,B_9318,C_9319) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_184046,plain,(
    ! [A_9882,A_9883,B_9884,C_9885] :
      ( r2_hidden(k1_mcart_1(A_9882),k2_zfmisc_1(A_9883,B_9884))
      | ~ r2_hidden(A_9882,k3_zfmisc_1(A_9883,B_9884,C_9885)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172179,c_54])).

tff(c_184098,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_64,c_184046])).

tff(c_184112,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_184098,c_52])).

tff(c_184131,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177060,c_184112])).

tff(c_184133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172178,c_184131])).

tff(c_184134,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_148985])).

tff(c_184136,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184134,c_89064])).

tff(c_185006,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_184978,c_184136])).

tff(c_184173,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_148986])).

tff(c_184177,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_89090,c_184173])).

tff(c_185003,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_184978,c_184177])).

tff(c_184153,plain,(
    ~ r1_tarski('#skF_6','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_148987])).

tff(c_184157,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_89090,c_184153])).

tff(c_185004,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_184978,c_184157])).

tff(c_185581,plain,(
    ! [A_9995,B_9996,C_9997,D_9998] :
      ( k6_mcart_1(A_9995,B_9996,C_9997,D_9998) = k2_mcart_1(k1_mcart_1(D_9998))
      | ~ m1_subset_1(D_9998,k3_zfmisc_1(A_9995,B_9996,C_9997))
      | k1_xboole_0 = C_9997
      | k1_xboole_0 = B_9996
      | k1_xboole_0 = A_9995 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_185584,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_185581])).

tff(c_185587,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_185006,c_185003,c_185004,c_185584])).

tff(c_184140,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184134,c_64])).

tff(c_184461,plain,(
    ! [A_9915,B_9916,C_9917] :
      ( r2_hidden(k1_mcart_1(A_9915),B_9916)
      | ~ r2_hidden(A_9915,k2_zfmisc_1(B_9916,C_9917)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_190327,plain,(
    ! [A_10198,A_10199,B_10200,C_10201] :
      ( r2_hidden(k1_mcart_1(A_10198),k2_zfmisc_1(A_10199,B_10200))
      | ~ r2_hidden(A_10198,k3_zfmisc_1(A_10199,B_10200,C_10201)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_184461])).

tff(c_190373,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_184140,c_190327])).

tff(c_190393,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_190373,c_52])).

tff(c_190411,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185587,c_190393])).

tff(c_190413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148870,c_190411])).

tff(c_190414,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_148986])).

tff(c_190417,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190414,c_148870])).

tff(c_190630,plain,(
    ! [A_10226,B_10227] :
      ( k3_xboole_0(A_10226,B_10227) = k1_xboole_0
      | ~ r1_xboole_0(A_10226,B_10227) ) ),
    inference(resolution,[status(thm)],[c_89102,c_149017])).

tff(c_190661,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_190630])).

tff(c_190481,plain,(
    ! [A_10210,B_10211] : r1_xboole_0(k3_xboole_0(A_10210,B_10211),k4_xboole_0(A_10210,B_10211)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148915,c_32])).

tff(c_190508,plain,(
    ! [A_10212,B_10213] : r1_xboole_0(k4_xboole_0(A_10212,B_10213),k3_xboole_0(A_10212,B_10213)) ),
    inference(resolution,[status(thm)],[c_190481,c_12])).

tff(c_190525,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_190508])).

tff(c_190724,plain,(
    ! [B_10231] : r1_xboole_0(B_10231,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190661,c_190525])).

tff(c_190743,plain,(
    ! [B_10231] : k3_xboole_0(B_10231,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_190724,c_149026])).

tff(c_190813,plain,(
    ! [B_10237] : k4_xboole_0(B_10237,k1_xboole_0) = B_10237 ),
    inference(resolution,[status(thm)],[c_190724,c_34])).

tff(c_190831,plain,(
    ! [B_10237] : k4_xboole_0(B_10237,B_10237) = k3_xboole_0(B_10237,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_190813,c_26])).

tff(c_191295,plain,(
    ! [B_10237] : k4_xboole_0(B_10237,B_10237) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190743,c_190831])).

tff(c_190432,plain,(
    ! [B_10202] :
      ( ~ r1_xboole_0(B_10202,B_10202)
      | v1_xboole_0(B_10202) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148953,c_89102])).

tff(c_190441,plain,(
    ! [A_4730] :
      ( v1_xboole_0(A_4730)
      | k4_xboole_0(A_4730,A_4730) != A_4730 ) ),
    inference(resolution,[status(thm)],[c_89060,c_190432])).

tff(c_191362,plain,(
    ! [A_10262] :
      ( v1_xboole_0(A_10262)
      | k1_xboole_0 != A_10262 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191295,c_190441])).

tff(c_191386,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_191362,c_184136])).

tff(c_191384,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(resolution,[status(thm)],[c_191362,c_184157])).

tff(c_190419,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190414,c_66])).

tff(c_191586,plain,(
    ! [A_10280,B_10281,C_10282,D_10283] :
      ( k7_mcart_1(A_10280,B_10281,C_10282,D_10283) = k2_mcart_1(D_10283)
      | ~ m1_subset_1(D_10283,k3_zfmisc_1(A_10280,B_10281,C_10282))
      | k1_xboole_0 = C_10282
      | k1_xboole_0 = B_10281
      | k1_xboole_0 = A_10280 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_191589,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_190419,c_191586])).

tff(c_191592,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_191386,c_191384,c_191589])).

tff(c_191665,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_191592])).

tff(c_191296,plain,(
    ! [A_4730] :
      ( v1_xboole_0(A_4730)
      | k1_xboole_0 != A_4730 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191295,c_190441])).

tff(c_192192,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191665,c_191296])).

tff(c_190764,plain,(
    ! [A_10233,B_10234,C_10235] :
      ( r2_hidden(k1_mcart_1(A_10233),B_10234)
      | ~ r2_hidden(A_10233,k2_zfmisc_1(B_10234,C_10235)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_195536,plain,(
    ! [B_10487,C_10488] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_10487,C_10488))),B_10487)
      | v1_xboole_0(k2_zfmisc_1(B_10487,C_10488)) ) ),
    inference(resolution,[status(thm)],[c_4,c_190764])).

tff(c_191106,plain,(
    ! [C_10247,B_10248,A_10249] :
      ( v1_xboole_0(C_10247)
      | ~ m1_subset_1(C_10247,k1_zfmisc_1(k2_zfmisc_1(B_10248,A_10249)))
      | ~ v1_xboole_0(A_10249) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_191113,plain,(
    ! [A_32,A_10249,B_10248] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_10249)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_10248,A_10249)) ) ),
    inference(resolution,[status(thm)],[c_40,c_191106])).

tff(c_191120,plain,(
    ! [A_10249,A_32,B_10248] :
      ( ~ v1_xboole_0(A_10249)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_10248,A_10249)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_191113])).

tff(c_195549,plain,(
    ! [A_10249,B_10248,C_10488] :
      ( ~ v1_xboole_0(A_10249)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_10248,A_10249),C_10488)) ) ),
    inference(resolution,[status(thm)],[c_195536,c_191120])).

tff(c_196094,plain,(
    ! [A_10506,B_10507,C_10508] :
      ( ~ v1_xboole_0(A_10506)
      | v1_xboole_0(k3_zfmisc_1(B_10507,A_10506,C_10508)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_195549])).

tff(c_184139,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184134,c_82])).

tff(c_196122,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_196094,c_184139])).

tff(c_196141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_192192,c_196122])).

tff(c_196143,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_191592])).

tff(c_196255,plain,(
    ! [A_10520,B_10521,C_10522,D_10523] :
      ( k6_mcart_1(A_10520,B_10521,C_10522,D_10523) = k2_mcart_1(k1_mcart_1(D_10523))
      | ~ m1_subset_1(D_10523,k3_zfmisc_1(A_10520,B_10521,C_10522))
      | k1_xboole_0 = C_10522
      | k1_xboole_0 = B_10521
      | k1_xboole_0 = A_10520 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_196258,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_190419,c_196255])).

tff(c_196261,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_191386,c_196143,c_191384,c_196258])).

tff(c_201069,plain,(
    ! [A_10751,A_10752,B_10753,C_10754] :
      ( r2_hidden(k1_mcart_1(A_10751),k2_zfmisc_1(A_10752,B_10753))
      | ~ r2_hidden(A_10751,k3_zfmisc_1(A_10752,B_10753,C_10754)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_190764])).

tff(c_201112,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_184140,c_201069])).

tff(c_201132,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_201112,c_52])).

tff(c_201150,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196261,c_201132])).

tff(c_201152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190417,c_201150])).

tff(c_201153,plain,(
    '#skF_6' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_148987])).

tff(c_201156,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201153,c_148870])).

tff(c_201372,plain,(
    ! [A_10781,B_10782] :
      ( k3_xboole_0(A_10781,B_10782) = k1_xboole_0
      | ~ r1_xboole_0(A_10781,B_10782) ) ),
    inference(resolution,[status(thm)],[c_89102,c_149017])).

tff(c_201403,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_201372])).

tff(c_201250,plain,(
    ! [A_10765,B_10766] : r1_xboole_0(k4_xboole_0(A_10765,B_10766),k3_xboole_0(A_10765,B_10766)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148915,c_91])).

tff(c_201267,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_201250])).

tff(c_201482,plain,(
    ! [B_10789] : r1_xboole_0(B_10789,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201403,c_201267])).

tff(c_201501,plain,(
    ! [B_10789] : k3_xboole_0(B_10789,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_201482,c_149026])).

tff(c_201748,plain,(
    ! [B_10799] : k4_xboole_0(B_10799,k1_xboole_0) = B_10799 ),
    inference(resolution,[status(thm)],[c_201482,c_34])).

tff(c_201770,plain,(
    ! [B_10799] : k4_xboole_0(B_10799,B_10799) = k3_xboole_0(B_10799,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_201748,c_26])).

tff(c_201797,plain,(
    ! [B_10799] : k4_xboole_0(B_10799,B_10799) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201501,c_201770])).

tff(c_201176,plain,(
    ! [B_10755] :
      ( ~ r1_xboole_0(B_10755,B_10755)
      | v1_xboole_0(B_10755) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148953,c_89102])).

tff(c_201186,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k4_xboole_0(B_30,B_30) != B_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_201176])).

tff(c_201885,plain,(
    ! [B_10804] :
      ( v1_xboole_0(B_10804)
      | k1_xboole_0 != B_10804 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201797,c_201186])).

tff(c_201909,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_201885,c_184136])).

tff(c_201171,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_148986])).

tff(c_201175,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_89090,c_201171])).

tff(c_201907,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_201885,c_201175])).

tff(c_201911,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(resolution,[status(thm)],[c_201885,c_148875])).

tff(c_201158,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_5','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201153,c_66])).

tff(c_202770,plain,(
    ! [A_10880,B_10881,C_10882,D_10883] :
      ( k6_mcart_1(A_10880,B_10881,C_10882,D_10883) = k2_mcart_1(k1_mcart_1(D_10883))
      | ~ m1_subset_1(D_10883,k3_zfmisc_1(A_10880,B_10881,C_10882))
      | k1_xboole_0 = C_10882
      | k1_xboole_0 = B_10881
      | k1_xboole_0 = A_10880 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_202773,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_201158,c_202770])).

tff(c_202776,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_201909,c_201907,c_201911,c_202773])).

tff(c_201309,plain,(
    ! [A_10772,B_10773,C_10774] : k2_zfmisc_1(k2_zfmisc_1(A_10772,B_10773),C_10774) = k3_zfmisc_1(A_10772,B_10773,C_10774) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_207141,plain,(
    ! [A_11083,A_11084,B_11085,C_11086] :
      ( r2_hidden(k1_mcart_1(A_11083),k2_zfmisc_1(A_11084,B_11085))
      | ~ r2_hidden(A_11083,k3_zfmisc_1(A_11084,B_11085,C_11086)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201309,c_54])).

tff(c_207180,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_184140,c_207141])).

tff(c_207198,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_207180,c_52])).

tff(c_207216,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202776,c_207198])).

tff(c_207218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201156,c_207216])).

tff(c_207219,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_148986])).

tff(c_207340,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207219,c_201156])).

tff(c_207399,plain,(
    ! [A_11108,B_11109] :
      ( k3_xboole_0(A_11108,B_11109) = k1_xboole_0
      | ~ r1_xboole_0(A_11108,B_11109) ) ),
    inference(resolution,[status(thm)],[c_89102,c_149017])).

tff(c_207426,plain,(
    ! [B_28,A_27] : k3_xboole_0(B_28,k4_xboole_0(A_27,B_28)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_207399])).

tff(c_207288,plain,(
    ! [A_11095,B_11096] : r1_xboole_0(k3_xboole_0(A_11095,B_11096),k4_xboole_0(A_11095,B_11096)) ),
    inference(superposition,[status(thm),theory(equality)],[c_148915,c_32])).

tff(c_207341,plain,(
    ! [A_11101,B_11102] : r1_xboole_0(k4_xboole_0(A_11101,B_11102),k3_xboole_0(A_11101,B_11102)) ),
    inference(resolution,[status(thm)],[c_207288,c_12])).

tff(c_207358,plain,(
    ! [B_28,A_27] : r1_xboole_0(B_28,k3_xboole_0(B_28,k4_xboole_0(A_27,B_28))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_207341])).

tff(c_207519,plain,(
    ! [B_11118] : r1_xboole_0(B_11118,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207426,c_207358])).

tff(c_207538,plain,(
    ! [B_11118] : k3_xboole_0(B_11118,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_207519,c_149026])).

tff(c_207602,plain,(
    ! [B_11123] : k4_xboole_0(B_11123,k1_xboole_0) = B_11123 ),
    inference(resolution,[status(thm)],[c_207519,c_34])).

tff(c_207623,plain,(
    ! [B_11123] : k4_xboole_0(B_11123,B_11123) = k3_xboole_0(B_11123,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_207602,c_26])).

tff(c_208019,plain,(
    ! [B_11123] : k4_xboole_0(B_11123,B_11123) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_207538,c_207623])).

tff(c_207234,plain,(
    ! [B_11087] :
      ( ~ r1_xboole_0(B_11087,B_11087)
      | v1_xboole_0(B_11087) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148953,c_89102])).

tff(c_207244,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k4_xboole_0(B_30,B_30) != B_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_207234])).

tff(c_208086,plain,(
    ! [B_11143] :
      ( v1_xboole_0(B_11143)
      | k1_xboole_0 != B_11143 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208019,c_207244])).

tff(c_208106,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_208086,c_184136])).

tff(c_208108,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(resolution,[status(thm)],[c_208086,c_148875])).

tff(c_207262,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207219,c_201158])).

tff(c_208385,plain,(
    ! [A_11171,B_11172,C_11173,D_11174] :
      ( k7_mcart_1(A_11171,B_11172,C_11173,D_11174) = k2_mcart_1(D_11174)
      | ~ m1_subset_1(D_11174,k3_zfmisc_1(A_11171,B_11172,C_11173))
      | k1_xboole_0 = C_11173
      | k1_xboole_0 = B_11172
      | k1_xboole_0 = A_11171 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_208388,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_207262,c_208385])).

tff(c_208391,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_208106,c_208108,c_208388])).

tff(c_208479,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_208391])).

tff(c_208020,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | k1_xboole_0 != B_30 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208019,c_207244])).

tff(c_208496,plain,(
    ! [B_30] :
      ( v1_xboole_0(B_30)
      | B_30 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208479,c_208020])).

tff(c_208110,plain,(
    ! [C_11144,B_11145,A_11146] :
      ( v1_xboole_0(C_11144)
      | ~ m1_subset_1(C_11144,k1_zfmisc_1(k2_zfmisc_1(B_11145,A_11146)))
      | ~ v1_xboole_0(A_11146) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_208117,plain,(
    ! [A_32,A_11146,B_11145] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_11146)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_11145,A_11146)) ) ),
    inference(resolution,[status(thm)],[c_40,c_208110])).

tff(c_208430,plain,(
    ! [A_11177,A_11178,B_11179] :
      ( ~ v1_xboole_0(A_11177)
      | ~ r2_hidden(A_11178,k2_zfmisc_1(B_11179,A_11177)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_208117])).

tff(c_208457,plain,(
    ! [A_11180,B_11181] :
      ( ~ v1_xboole_0(A_11180)
      | v1_xboole_0(k2_zfmisc_1(B_11181,A_11180)) ) ),
    inference(resolution,[status(thm)],[c_4,c_208430])).

tff(c_207918,plain,(
    ! [C_11134,A_11135,B_11136] :
      ( v1_xboole_0(C_11134)
      | ~ m1_subset_1(C_11134,k1_zfmisc_1(k2_zfmisc_1(A_11135,B_11136)))
      | ~ v1_xboole_0(A_11135) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_207925,plain,(
    ! [A_32,A_11135,B_11136] :
      ( v1_xboole_0(k1_tarski(A_32))
      | ~ v1_xboole_0(A_11135)
      | ~ r2_hidden(A_32,k2_zfmisc_1(A_11135,B_11136)) ) ),
    inference(resolution,[status(thm)],[c_40,c_207918])).

tff(c_208336,plain,(
    ! [A_11164,A_11165,B_11166] :
      ( ~ v1_xboole_0(A_11164)
      | ~ r2_hidden(A_11165,k2_zfmisc_1(A_11164,B_11166)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_207925])).

tff(c_208360,plain,(
    ! [A_11167,B_11168] :
      ( ~ v1_xboole_0(A_11167)
      | v1_xboole_0(k2_zfmisc_1(A_11167,B_11168)) ) ),
    inference(resolution,[status(thm)],[c_4,c_208336])).

tff(c_149011,plain,(
    ! [A_4740] :
      ( k1_xboole_0 = A_4740
      | ~ v1_xboole_0(A_4740) ) ),
    inference(resolution,[status(thm)],[c_89090,c_148994])).

tff(c_208373,plain,(
    ! [A_11167,B_11168] :
      ( k2_zfmisc_1(A_11167,B_11168) = k1_xboole_0
      | ~ v1_xboole_0(A_11167) ) ),
    inference(resolution,[status(thm)],[c_208360,c_149011])).

tff(c_208459,plain,(
    ! [B_11181,A_11180,B_11168] :
      ( k2_zfmisc_1(k2_zfmisc_1(B_11181,A_11180),B_11168) = k1_xboole_0
      | ~ v1_xboole_0(A_11180) ) ),
    inference(resolution,[status(thm)],[c_208457,c_208373])).

tff(c_208474,plain,(
    ! [B_11181,A_11180,B_11168] :
      ( k3_zfmisc_1(B_11181,A_11180,B_11168) = k1_xboole_0
      | ~ v1_xboole_0(A_11180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_208459])).

tff(c_211377,plain,(
    ! [B_11340,A_11341,B_11342] :
      ( k3_zfmisc_1(B_11340,A_11341,B_11342) = '#skF_8'
      | ~ v1_xboole_0(A_11341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208479,c_208474])).

tff(c_211674,plain,(
    ! [B_11340,B_11342] : k3_zfmisc_1(B_11340,'#skF_8',B_11342) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_208496,c_211377])).

tff(c_208105,plain,(
    k3_zfmisc_1('#skF_4','#skF_8','#skF_9') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_208086,c_184139])).

tff(c_208492,plain,(
    k3_zfmisc_1('#skF_4','#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208479,c_208105])).

tff(c_211682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211674,c_208492])).

tff(c_211684,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_208391])).

tff(c_211939,plain,(
    ! [A_11385,B_11386,C_11387,D_11388] :
      ( k6_mcart_1(A_11385,B_11386,C_11387,D_11388) = k2_mcart_1(k1_mcart_1(D_11388))
      | ~ m1_subset_1(D_11388,k3_zfmisc_1(A_11385,B_11386,C_11387))
      | k1_xboole_0 = C_11387
      | k1_xboole_0 = B_11386
      | k1_xboole_0 = A_11385 ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_211942,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_207262,c_211939])).

tff(c_211945,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_208106,c_211684,c_208108,c_211942])).

tff(c_207365,plain,(
    ! [A_11103,B_11104,C_11105] :
      ( r2_hidden(k1_mcart_1(A_11103),B_11104)
      | ~ r2_hidden(A_11103,k2_zfmisc_1(B_11104,C_11105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_218073,plain,(
    ! [A_11680,A_11681,B_11682,C_11683] :
      ( r2_hidden(k1_mcart_1(A_11680),k2_zfmisc_1(A_11681,B_11682))
      | ~ r2_hidden(A_11680,k3_zfmisc_1(A_11681,B_11682,C_11683)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_207365])).

tff(c_218119,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_184140,c_218073])).

tff(c_218135,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_218119,c_52])).

tff(c_218154,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211945,c_218135])).

tff(c_218156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_207340,c_218154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:58:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.94/16.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.62/16.99  
% 26.62/16.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.62/17.00  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 26.62/17.00  
% 26.62/17.00  %Foreground sorts:
% 26.62/17.00  
% 26.62/17.00  
% 26.62/17.00  %Background operators:
% 26.62/17.00  
% 26.62/17.00  
% 26.62/17.00  %Foreground operators:
% 26.62/17.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.62/17.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.62/17.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 26.62/17.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.62/17.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 26.62/17.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.62/17.00  tff('#skF_7', type, '#skF_7': $i).
% 26.62/17.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 26.62/17.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.62/17.00  tff('#skF_10', type, '#skF_10': $i).
% 26.62/17.00  tff('#skF_5', type, '#skF_5': $i).
% 26.62/17.00  tff('#skF_6', type, '#skF_6': $i).
% 26.62/17.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 26.62/17.00  tff('#skF_9', type, '#skF_9': $i).
% 26.62/17.00  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 26.62/17.00  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 26.62/17.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.62/17.00  tff('#skF_8', type, '#skF_8': $i).
% 26.62/17.00  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 26.62/17.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.62/17.00  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 26.62/17.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 26.62/17.00  tff('#skF_4', type, '#skF_4': $i).
% 26.62/17.00  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 26.62/17.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.62/17.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 26.62/17.00  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 26.62/17.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 26.62/17.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 26.62/17.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.62/17.00  
% 27.04/17.08  tff(f_82, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 27.04/17.08  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 27.04/17.08  tff(f_86, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 27.04/17.08  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 27.04/17.08  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 27.04/17.08  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 27.04/17.08  tff(f_64, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 27.04/17.08  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 27.04/17.08  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 27.04/17.08  tff(f_113, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 27.04/17.08  tff(f_89, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 27.04/17.08  tff(f_93, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 27.04/17.08  tff(f_111, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 27.04/17.08  tff(f_159, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 27.04/17.08  tff(f_97, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 27.04/17.08  tff(f_139, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 27.04/17.08  tff(f_119, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 27.04/17.08  tff(f_104, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 27.04/17.08  tff(c_32, plain, (![A_27, B_28]: (r1_xboole_0(k4_xboole_0(A_27, B_28), B_28))), inference(cnfTransformation, [status(thm)], [f_82])).
% 27.04/17.08  tff(c_88, plain, (![B_74, A_75]: (r1_xboole_0(B_74, A_75) | ~r1_xboole_0(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.04/17.08  tff(c_91, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k4_xboole_0(A_27, B_28)))), inference(resolution, [status(thm)], [c_32, c_88])).
% 27.04/17.08  tff(c_97, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=A_78 | ~r1_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.04/17.08  tff(c_104, plain, (![B_28, A_27]: (k4_xboole_0(B_28, k4_xboole_0(A_27, B_28))=B_28)), inference(resolution, [status(thm)], [c_91, c_97])).
% 27.04/17.08  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.04/17.08  tff(c_89092, plain, (![A_4744, B_4745, C_4746]: (~r1_xboole_0(A_4744, B_4745) | ~r2_hidden(C_4746, k3_xboole_0(A_4744, B_4745)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.04/17.08  tff(c_89102, plain, (![A_4744, B_4745]: (~r1_xboole_0(A_4744, B_4745) | v1_xboole_0(k3_xboole_0(A_4744, B_4745)))), inference(resolution, [status(thm)], [c_4, c_89092])).
% 27.04/17.08  tff(c_89080, plain, (![A_4740, B_4741]: (r2_hidden('#skF_2'(A_4740, B_4741), A_4740) | r1_tarski(A_4740, B_4741))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.04/17.08  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.04/17.08  tff(c_89090, plain, (![A_4740, B_4741]: (~v1_xboole_0(A_4740) | r1_tarski(A_4740, B_4741))), inference(resolution, [status(thm)], [c_89080, c_2])).
% 27.04/17.08  tff(c_24, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 27.04/17.08  tff(c_89105, plain, (![B_4749, A_4750]: (B_4749=A_4750 | ~r1_tarski(B_4749, A_4750) | ~r1_tarski(A_4750, B_4749))), inference(cnfTransformation, [status(thm)], [f_62])).
% 27.04/17.08  tff(c_89130, plain, (![A_4751]: (k1_xboole_0=A_4751 | ~r1_tarski(A_4751, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_89105])).
% 27.04/17.08  tff(c_89153, plain, (![A_4752]: (k1_xboole_0=A_4752 | ~v1_xboole_0(A_4752))), inference(resolution, [status(thm)], [c_89090, c_89130])).
% 27.04/17.08  tff(c_140143, plain, (![A_7641, B_7642]: (k3_xboole_0(A_7641, B_7642)=k1_xboole_0 | ~r1_xboole_0(A_7641, B_7642))), inference(resolution, [status(thm)], [c_89102, c_89153])).
% 27.04/17.08  tff(c_140168, plain, (![B_7643, A_7644]: (k3_xboole_0(B_7643, k4_xboole_0(A_7644, B_7643))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_140143])).
% 27.04/17.08  tff(c_139946, plain, (![A_7620, B_7621]: (k4_xboole_0(A_7620, k4_xboole_0(A_7620, B_7621))=k3_xboole_0(A_7620, B_7621))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.08  tff(c_139962, plain, (![A_7620, B_7621]: (r1_xboole_0(k4_xboole_0(A_7620, B_7621), k3_xboole_0(A_7620, B_7621)))), inference(superposition, [status(thm), theory('equality')], [c_139946, c_91])).
% 27.04/17.08  tff(c_140173, plain, (![B_7643, A_7644]: (r1_xboole_0(k4_xboole_0(B_7643, k4_xboole_0(A_7644, B_7643)), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_140168, c_139962])).
% 27.04/17.08  tff(c_140212, plain, (![B_7648]: (r1_xboole_0(B_7648, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_140173])).
% 27.04/17.08  tff(c_89157, plain, (![A_4744, B_4745]: (k3_xboole_0(A_4744, B_4745)=k1_xboole_0 | ~r1_xboole_0(A_4744, B_4745))), inference(resolution, [status(thm)], [c_89102, c_89153])).
% 27.04/17.08  tff(c_140231, plain, (![B_7648]: (k3_xboole_0(B_7648, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_140212, c_89157])).
% 27.04/17.08  tff(c_34, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=A_29 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.04/17.08  tff(c_140355, plain, (![B_7653]: (k4_xboole_0(B_7653, k1_xboole_0)=B_7653)), inference(resolution, [status(thm)], [c_140212, c_34])).
% 27.04/17.08  tff(c_26, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.08  tff(c_140380, plain, (![B_7653]: (k4_xboole_0(B_7653, B_7653)=k3_xboole_0(B_7653, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_140355, c_26])).
% 27.04/17.08  tff(c_140747, plain, (![B_7653]: (k4_xboole_0(B_7653, B_7653)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_140231, c_140380])).
% 27.04/17.08  tff(c_89053, plain, (![A_4730, B_4731]: (r1_xboole_0(A_4730, B_4731) | k4_xboole_0(A_4730, B_4731)!=A_4730)), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.04/17.08  tff(c_12, plain, (![B_11, A_10]: (r1_xboole_0(B_11, A_10) | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 27.04/17.08  tff(c_89060, plain, (![B_4731, A_4730]: (r1_xboole_0(B_4731, A_4730) | k4_xboole_0(A_4730, B_4731)!=A_4730)), inference(resolution, [status(thm)], [c_89053, c_12])).
% 27.04/17.08  tff(c_139986, plain, (![B_7622]: (k3_xboole_0(B_7622, B_7622)=B_7622)), inference(superposition, [status(thm), theory('equality')], [c_139946, c_104])).
% 27.04/17.08  tff(c_140007, plain, (![B_7623]: (~r1_xboole_0(B_7623, B_7623) | v1_xboole_0(B_7623))), inference(superposition, [status(thm), theory('equality')], [c_139986, c_89102])).
% 27.04/17.08  tff(c_140016, plain, (![A_4730]: (v1_xboole_0(A_4730) | k4_xboole_0(A_4730, A_4730)!=A_4730)), inference(resolution, [status(thm)], [c_89060, c_140007])).
% 27.04/17.08  tff(c_140748, plain, (![A_4730]: (v1_xboole_0(A_4730) | k1_xboole_0!=A_4730)), inference(demodulation, [status(thm), theory('equality')], [c_140747, c_140016])).
% 27.04/17.08  tff(c_50, plain, (![A_44, B_45, C_46]: (k2_zfmisc_1(k2_zfmisc_1(A_44, B_45), C_46)=k3_zfmisc_1(A_44, B_45, C_46))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.08  tff(c_38, plain, (![A_31]: (~v1_xboole_0(k1_tarski(A_31)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 27.04/17.08  tff(c_40, plain, (![A_32, B_33]: (m1_subset_1(k1_tarski(A_32), k1_zfmisc_1(B_33)) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_93])).
% 27.04/17.08  tff(c_141516, plain, (![C_7722, B_7723, A_7724]: (v1_xboole_0(C_7722) | ~m1_subset_1(C_7722, k1_zfmisc_1(k2_zfmisc_1(B_7723, A_7724))) | ~v1_xboole_0(A_7724))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.08  tff(c_141523, plain, (![A_32, A_7724, B_7723]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_7724) | ~r2_hidden(A_32, k2_zfmisc_1(B_7723, A_7724)))), inference(resolution, [status(thm)], [c_40, c_141516])).
% 27.04/17.08  tff(c_141684, plain, (![A_7731, A_7732, B_7733]: (~v1_xboole_0(A_7731) | ~r2_hidden(A_7732, k2_zfmisc_1(B_7733, A_7731)))), inference(negUnitSimplification, [status(thm)], [c_38, c_141523])).
% 27.04/17.08  tff(c_141703, plain, (![A_7734, B_7735]: (~v1_xboole_0(A_7734) | v1_xboole_0(k2_zfmisc_1(B_7735, A_7734)))), inference(resolution, [status(thm)], [c_4, c_141684])).
% 27.04/17.08  tff(c_144939, plain, (![C_7919, A_7920, B_7921]: (~v1_xboole_0(C_7919) | v1_xboole_0(k3_zfmisc_1(A_7920, B_7921, C_7919)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_141703])).
% 27.04/17.08  tff(c_123768, plain, (![A_6727, B_6728]: (k3_xboole_0(A_6727, B_6728)=k1_xboole_0 | ~r1_xboole_0(A_6727, B_6728))), inference(resolution, [status(thm)], [c_89102, c_89153])).
% 27.04/17.08  tff(c_123795, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_123768])).
% 27.04/17.08  tff(c_123583, plain, (![A_6708, B_6709]: (k4_xboole_0(A_6708, k4_xboole_0(A_6708, B_6709))=k3_xboole_0(A_6708, B_6709))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.08  tff(c_123678, plain, (![A_6717, B_6718]: (r1_xboole_0(k4_xboole_0(A_6717, B_6718), k3_xboole_0(A_6717, B_6718)))), inference(superposition, [status(thm), theory('equality')], [c_123583, c_91])).
% 27.04/17.08  tff(c_123692, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_123678])).
% 27.04/17.08  tff(c_123829, plain, (![B_6731]: (r1_xboole_0(B_6731, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_123795, c_123692])).
% 27.04/17.08  tff(c_123848, plain, (![B_6731]: (k3_xboole_0(B_6731, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_123829, c_89157])).
% 27.04/17.08  tff(c_123960, plain, (![B_6741]: (k4_xboole_0(B_6741, k1_xboole_0)=B_6741)), inference(resolution, [status(thm)], [c_123829, c_34])).
% 27.04/17.08  tff(c_123981, plain, (![B_6741]: (k4_xboole_0(B_6741, B_6741)=k3_xboole_0(B_6741, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_123960, c_26])).
% 27.04/17.08  tff(c_124001, plain, (![B_6741]: (k4_xboole_0(B_6741, B_6741)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_123848, c_123981])).
% 27.04/17.08  tff(c_36, plain, (![A_29, B_30]: (r1_xboole_0(A_29, B_30) | k4_xboole_0(A_29, B_30)!=A_29)), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.04/17.08  tff(c_123618, plain, (![B_6710]: (k3_xboole_0(B_6710, B_6710)=B_6710)), inference(superposition, [status(thm), theory('equality')], [c_123583, c_104])).
% 27.04/17.08  tff(c_123634, plain, (![B_6711]: (~r1_xboole_0(B_6711, B_6711) | v1_xboole_0(B_6711))), inference(superposition, [status(thm), theory('equality')], [c_123618, c_89102])).
% 27.04/17.08  tff(c_123644, plain, (![B_30]: (v1_xboole_0(B_30) | k4_xboole_0(B_30, B_30)!=B_30)), inference(resolution, [status(thm)], [c_36, c_123634])).
% 27.04/17.08  tff(c_124219, plain, (![B_6749]: (v1_xboole_0(B_6749) | k1_xboole_0!=B_6749)), inference(demodulation, [status(thm), theory('equality')], [c_124001, c_123644])).
% 27.04/17.08  tff(c_72, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 27.04/17.08  tff(c_106, plain, (![A_80, B_81]: (r1_tarski(A_80, B_81) | ~m1_subset_1(A_80, k1_zfmisc_1(B_81)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 27.04/17.08  tff(c_118, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_106])).
% 27.04/17.08  tff(c_89122, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_118, c_89105])).
% 27.04/17.08  tff(c_117075, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_89122])).
% 27.04/17.08  tff(c_117079, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_89090, c_117075])).
% 27.04/17.08  tff(c_124238, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_124219, c_117079])).
% 27.04/17.08  tff(c_124144, plain, (![B_30]: (v1_xboole_0(B_30) | k1_xboole_0!=B_30)), inference(demodulation, [status(thm), theory('equality')], [c_124001, c_123644])).
% 27.04/17.08  tff(c_124475, plain, (![C_6772, B_6773, A_6774]: (v1_xboole_0(C_6772) | ~m1_subset_1(C_6772, k1_zfmisc_1(k2_zfmisc_1(B_6773, A_6774))) | ~v1_xboole_0(A_6774))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.08  tff(c_124482, plain, (![A_32, A_6774, B_6773]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_6774) | ~r2_hidden(A_32, k2_zfmisc_1(B_6773, A_6774)))), inference(resolution, [status(thm)], [c_40, c_124475])).
% 27.04/17.08  tff(c_124491, plain, (![A_6775, A_6776, B_6777]: (~v1_xboole_0(A_6775) | ~r2_hidden(A_6776, k2_zfmisc_1(B_6777, A_6775)))), inference(negUnitSimplification, [status(thm)], [c_38, c_124482])).
% 27.04/17.08  tff(c_124505, plain, (![A_6778, B_6779]: (~v1_xboole_0(A_6778) | v1_xboole_0(k2_zfmisc_1(B_6779, A_6778)))), inference(resolution, [status(thm)], [c_4, c_124491])).
% 27.04/17.08  tff(c_124673, plain, (![C_6790, A_6791, B_6792]: (~v1_xboole_0(C_6790) | v1_xboole_0(k3_zfmisc_1(A_6791, B_6792, C_6790)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_124505])).
% 27.04/17.08  tff(c_64, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 27.04/17.08  tff(c_82, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_64, c_2])).
% 27.04/17.08  tff(c_124690, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_124673, c_82])).
% 27.04/17.08  tff(c_124713, plain, (k1_xboole_0!='#skF_9'), inference(resolution, [status(thm)], [c_124144, c_124690])).
% 27.04/17.08  tff(c_117372, plain, (![A_6344, B_6345]: (k3_xboole_0(A_6344, B_6345)=k1_xboole_0 | ~r1_xboole_0(A_6344, B_6345))), inference(resolution, [status(thm)], [c_89102, c_89153])).
% 27.04/17.08  tff(c_117403, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_117372])).
% 27.04/17.08  tff(c_117085, plain, (![A_6312, B_6313]: (k4_xboole_0(A_6312, k4_xboole_0(A_6312, B_6313))=k3_xboole_0(A_6312, B_6313))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.08  tff(c_117244, plain, (![A_6328, B_6329]: (r1_xboole_0(k4_xboole_0(A_6328, B_6329), k3_xboole_0(A_6328, B_6329)))), inference(superposition, [status(thm), theory('equality')], [c_117085, c_91])).
% 27.04/17.08  tff(c_117261, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_117244])).
% 27.04/17.08  tff(c_117438, plain, (![B_6348]: (r1_xboole_0(B_6348, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_117403, c_117261])).
% 27.04/17.08  tff(c_117459, plain, (![B_6348]: (k3_xboole_0(B_6348, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_117438, c_89157])).
% 27.04/17.08  tff(c_117600, plain, (![B_6358]: (k4_xboole_0(B_6358, k1_xboole_0)=B_6358)), inference(resolution, [status(thm)], [c_117438, c_34])).
% 27.04/17.08  tff(c_117625, plain, (![B_6358]: (k4_xboole_0(B_6358, B_6358)=k3_xboole_0(B_6358, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_117600, c_26])).
% 27.04/17.08  tff(c_117961, plain, (![B_6358]: (k4_xboole_0(B_6358, B_6358)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_117459, c_117625])).
% 27.04/17.08  tff(c_117120, plain, (![A_6314]: (k3_xboole_0(A_6314, A_6314)=A_6314)), inference(superposition, [status(thm), theory('equality')], [c_104, c_117085])).
% 27.04/17.08  tff(c_117140, plain, (![A_6315]: (~r1_xboole_0(A_6315, A_6315) | v1_xboole_0(A_6315))), inference(superposition, [status(thm), theory('equality')], [c_117120, c_89102])).
% 27.04/17.08  tff(c_117149, plain, (![A_4730]: (v1_xboole_0(A_4730) | k4_xboole_0(A_4730, A_4730)!=A_4730)), inference(resolution, [status(thm)], [c_89060, c_117140])).
% 27.04/17.08  tff(c_118028, plain, (![A_6379]: (v1_xboole_0(A_6379) | k1_xboole_0!=A_6379)), inference(demodulation, [status(thm), theory('equality')], [c_117961, c_117149])).
% 27.04/17.08  tff(c_118051, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_118028, c_117079])).
% 27.04/17.08  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 27.04/17.08  tff(c_117, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_106])).
% 27.04/17.08  tff(c_89123, plain, ('#skF_5'='#skF_8' | ~r1_tarski('#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_117, c_89105])).
% 27.04/17.08  tff(c_117080, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_89123])).
% 27.04/17.08  tff(c_117084, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_89090, c_117080])).
% 27.04/17.08  tff(c_118050, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_118028, c_117084])).
% 27.04/17.08  tff(c_107896, plain, (![A_5827, B_5828]: (k3_xboole_0(A_5827, B_5828)=k1_xboole_0 | ~r1_xboole_0(A_5827, B_5828))), inference(resolution, [status(thm)], [c_89102, c_89153])).
% 27.04/17.08  tff(c_107927, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_107896])).
% 27.04/17.08  tff(c_89159, plain, (![A_4753, B_4754]: (k4_xboole_0(A_4753, k4_xboole_0(A_4753, B_4754))=k3_xboole_0(A_4753, B_4754))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.08  tff(c_107733, plain, (![A_5807, B_5808]: (r1_xboole_0(k3_xboole_0(A_5807, B_5808), k4_xboole_0(A_5807, B_5808)))), inference(superposition, [status(thm), theory('equality')], [c_89159, c_32])).
% 27.04/17.08  tff(c_107781, plain, (![A_5813, B_5814]: (r1_xboole_0(k4_xboole_0(A_5813, B_5814), k3_xboole_0(A_5813, B_5814)))), inference(resolution, [status(thm)], [c_107733, c_12])).
% 27.04/17.08  tff(c_107798, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_107781])).
% 27.04/17.08  tff(c_107981, plain, (![B_5834]: (r1_xboole_0(B_5834, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_107927, c_107798])).
% 27.04/17.08  tff(c_108004, plain, (![B_5834]: (k3_xboole_0(B_5834, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_107981, c_89157])).
% 27.04/17.08  tff(c_108208, plain, (![B_5844]: (k4_xboole_0(B_5844, k1_xboole_0)=B_5844)), inference(resolution, [status(thm)], [c_107981, c_34])).
% 27.04/17.08  tff(c_108233, plain, (![B_5844]: (k4_xboole_0(B_5844, B_5844)=k3_xboole_0(B_5844, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_108208, c_26])).
% 27.04/17.08  tff(c_108258, plain, (![B_5844]: (k4_xboole_0(B_5844, B_5844)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108004, c_108233])).
% 27.04/17.08  tff(c_89198, plain, (![A_4755]: (k3_xboole_0(A_4755, A_4755)=A_4755)), inference(superposition, [status(thm), theory('equality')], [c_104, c_89159])).
% 27.04/17.08  tff(c_107668, plain, (![A_5800]: (~r1_xboole_0(A_5800, A_5800) | v1_xboole_0(A_5800))), inference(superposition, [status(thm), theory('equality')], [c_89198, c_89102])).
% 27.04/17.08  tff(c_107678, plain, (![B_30]: (v1_xboole_0(B_30) | k4_xboole_0(B_30, B_30)!=B_30)), inference(resolution, [status(thm)], [c_36, c_107668])).
% 27.04/17.08  tff(c_108418, plain, (![B_5852]: (v1_xboole_0(B_5852) | k1_xboole_0!=B_5852)), inference(demodulation, [status(thm), theory('equality')], [c_108258, c_107678])).
% 27.04/17.08  tff(c_93821, plain, (![A_5057, B_5058]: (k3_xboole_0(A_5057, B_5058)=k1_xboole_0 | ~r1_xboole_0(A_5057, B_5058))), inference(resolution, [status(thm)], [c_89102, c_89153])).
% 27.04/17.08  tff(c_93852, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_93821])).
% 27.04/17.08  tff(c_93702, plain, (![A_5043, B_5044]: (r1_xboole_0(k4_xboole_0(A_5043, B_5044), k3_xboole_0(A_5043, B_5044)))), inference(superposition, [status(thm), theory('equality')], [c_89159, c_91])).
% 27.04/17.08  tff(c_93719, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_93702])).
% 27.04/17.08  tff(c_93887, plain, (![B_5061]: (r1_xboole_0(B_5061, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_93852, c_93719])).
% 27.04/17.08  tff(c_93906, plain, (![B_5061]: (k3_xboole_0(B_5061, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_93887, c_89157])).
% 27.04/17.08  tff(c_94174, plain, (![B_5074]: (k4_xboole_0(B_5074, k1_xboole_0)=B_5074)), inference(resolution, [status(thm)], [c_93887, c_34])).
% 27.04/17.08  tff(c_94199, plain, (![B_5074]: (k4_xboole_0(B_5074, B_5074)=k3_xboole_0(B_5074, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_94174, c_26])).
% 27.04/17.08  tff(c_94225, plain, (![B_5074]: (k4_xboole_0(B_5074, B_5074)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_93906, c_94199])).
% 27.04/17.08  tff(c_93594, plain, (![A_5030]: (~r1_xboole_0(A_5030, A_5030) | v1_xboole_0(A_5030))), inference(superposition, [status(thm), theory('equality')], [c_89198, c_89102])).
% 27.04/17.08  tff(c_93604, plain, (![B_30]: (v1_xboole_0(B_30) | k4_xboole_0(B_30, B_30)!=B_30)), inference(resolution, [status(thm)], [c_36, c_93594])).
% 27.04/17.08  tff(c_94310, plain, (![B_5077]: (v1_xboole_0(B_5077) | k1_xboole_0!=B_5077)), inference(demodulation, [status(thm), theory('equality')], [c_94225, c_93604])).
% 27.04/17.08  tff(c_89213, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_89122])).
% 27.04/17.08  tff(c_89217, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_89090, c_89213])).
% 27.04/17.08  tff(c_94332, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_94310, c_89217])).
% 27.04/17.08  tff(c_68, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 27.04/17.08  tff(c_116, plain, (r1_tarski('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_106])).
% 27.04/17.08  tff(c_89124, plain, ('#skF_6'='#skF_9' | ~r1_tarski('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_116, c_89105])).
% 27.04/17.08  tff(c_89158, plain, (~r1_tarski('#skF_6', '#skF_9')), inference(splitLeft, [status(thm)], [c_89124])).
% 27.04/17.08  tff(c_89197, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_89090, c_89158])).
% 27.04/17.08  tff(c_94333, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_94310, c_89197])).
% 27.04/17.08  tff(c_89476, plain, (![A_4791, B_4792]: (k3_xboole_0(A_4791, B_4792)=k1_xboole_0 | ~r1_xboole_0(A_4791, B_4792))), inference(resolution, [status(thm)], [c_89102, c_89153])).
% 27.04/17.08  tff(c_89507, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_89476])).
% 27.04/17.08  tff(c_89328, plain, (![A_4771, B_4772]: (r1_xboole_0(k4_xboole_0(A_4771, B_4772), k3_xboole_0(A_4771, B_4772)))), inference(superposition, [status(thm), theory('equality')], [c_89159, c_91])).
% 27.04/17.08  tff(c_89345, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_89328])).
% 27.04/17.08  tff(c_89582, plain, (![B_4797]: (r1_xboole_0(B_4797, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_89507, c_89345])).
% 27.04/17.08  tff(c_89601, plain, (![B_4797]: (k3_xboole_0(B_4797, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_89582, c_89157])).
% 27.04/17.08  tff(c_89783, plain, (![B_4805]: (k4_xboole_0(B_4805, k1_xboole_0)=B_4805)), inference(resolution, [status(thm)], [c_89582, c_34])).
% 27.04/17.08  tff(c_89808, plain, (![B_4805]: (k4_xboole_0(B_4805, B_4805)=k3_xboole_0(B_4805, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_89783, c_26])).
% 27.04/17.08  tff(c_89833, plain, (![B_4805]: (k4_xboole_0(B_4805, B_4805)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_89601, c_89808])).
% 27.04/17.08  tff(c_89241, plain, (![A_4758]: (~r1_xboole_0(A_4758, A_4758) | v1_xboole_0(A_4758))), inference(superposition, [status(thm), theory('equality')], [c_89198, c_89102])).
% 27.04/17.08  tff(c_89251, plain, (![B_30]: (v1_xboole_0(B_30) | k4_xboole_0(B_30, B_30)!=B_30)), inference(resolution, [status(thm)], [c_36, c_89241])).
% 27.04/17.08  tff(c_89986, plain, (![B_4812]: (v1_xboole_0(B_4812) | k1_xboole_0!=B_4812)), inference(demodulation, [status(thm), theory('equality')], [c_89833, c_89251])).
% 27.04/17.08  tff(c_90012, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_89986, c_89217])).
% 27.04/17.08  tff(c_89219, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_89123])).
% 27.04/17.08  tff(c_89223, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_89090, c_89219])).
% 27.04/17.08  tff(c_90011, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_89986, c_89223])).
% 27.04/17.08  tff(c_90013, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_89986, c_89197])).
% 27.04/17.08  tff(c_66, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 27.04/17.08  tff(c_90308, plain, (![A_4832, B_4833, C_4834, D_4835]: (k7_mcart_1(A_4832, B_4833, C_4834, D_4835)=k2_mcart_1(D_4835) | ~m1_subset_1(D_4835, k3_zfmisc_1(A_4832, B_4833, C_4834)) | k1_xboole_0=C_4834 | k1_xboole_0=B_4833 | k1_xboole_0=A_4832)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.08  tff(c_90311, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_90308])).
% 27.04/17.08  tff(c_90314, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_90012, c_90011, c_90013, c_90311])).
% 27.04/17.08  tff(c_62, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9') | ~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8') | ~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_159])).
% 27.04/17.08  tff(c_119, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_62])).
% 27.04/17.08  tff(c_199, plain, (![A_93, B_94, C_95]: (~r1_xboole_0(A_93, B_94) | ~r2_hidden(C_95, k3_xboole_0(A_93, B_94)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.04/17.08  tff(c_204, plain, (![A_93, B_94]: (~r1_xboole_0(A_93, B_94) | v1_xboole_0(k3_xboole_0(A_93, B_94)))), inference(resolution, [status(thm)], [c_4, c_199])).
% 27.04/17.08  tff(c_268, plain, (![A_102, B_103]: (r2_hidden('#skF_2'(A_102, B_103), A_102) | r1_tarski(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.04/17.08  tff(c_278, plain, (![A_104, B_105]: (~v1_xboole_0(A_104) | r1_tarski(A_104, B_105))), inference(resolution, [status(thm)], [c_268, c_2])).
% 27.04/17.08  tff(c_164, plain, (![B_90, A_91]: (B_90=A_91 | ~r1_tarski(B_90, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_62])).
% 27.04/17.08  tff(c_182, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_164])).
% 27.04/17.08  tff(c_299, plain, (![A_106]: (k1_xboole_0=A_106 | ~v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_278, c_182])).
% 27.04/17.08  tff(c_489, plain, (![A_134, B_135]: (k3_xboole_0(A_134, B_135)=k1_xboole_0 | ~r1_xboole_0(A_134, B_135))), inference(resolution, [status(thm)], [c_204, c_299])).
% 27.04/17.08  tff(c_514, plain, (![B_136, A_137]: (k3_xboole_0(B_136, k4_xboole_0(A_137, B_136))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_489])).
% 27.04/17.08  tff(c_206, plain, (![A_98, B_99]: (k4_xboole_0(A_98, k4_xboole_0(A_98, B_99))=k3_xboole_0(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.08  tff(c_336, plain, (![A_114, B_115]: (r1_xboole_0(k3_xboole_0(A_114, B_115), k4_xboole_0(A_114, B_115)))), inference(superposition, [status(thm), theory('equality')], [c_206, c_32])).
% 27.04/17.08  tff(c_356, plain, (![A_114, B_115]: (r1_xboole_0(k4_xboole_0(A_114, B_115), k3_xboole_0(A_114, B_115)))), inference(resolution, [status(thm)], [c_336, c_12])).
% 27.04/17.08  tff(c_519, plain, (![B_136, A_137]: (r1_xboole_0(k4_xboole_0(B_136, k4_xboole_0(A_137, B_136)), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_514, c_356])).
% 27.04/17.08  tff(c_554, plain, (![B_141]: (r1_xboole_0(B_141, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_519])).
% 27.04/17.08  tff(c_303, plain, (![A_93, B_94]: (k3_xboole_0(A_93, B_94)=k1_xboole_0 | ~r1_xboole_0(A_93, B_94))), inference(resolution, [status(thm)], [c_204, c_299])).
% 27.04/17.08  tff(c_573, plain, (![B_141]: (k3_xboole_0(B_141, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_554, c_303])).
% 27.04/17.08  tff(c_697, plain, (![B_146]: (k4_xboole_0(B_146, k1_xboole_0)=B_146)), inference(resolution, [status(thm)], [c_554, c_34])).
% 27.04/17.08  tff(c_722, plain, (![B_146]: (k4_xboole_0(B_146, B_146)=k3_xboole_0(B_146, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_697, c_26])).
% 27.04/17.08  tff(c_1015, plain, (![B_146]: (k4_xboole_0(B_146, B_146)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_573, c_722])).
% 27.04/17.08  tff(c_148, plain, (![A_86, B_87]: (r1_xboole_0(A_86, B_87) | k4_xboole_0(A_86, B_87)!=A_86)), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.04/17.08  tff(c_155, plain, (![B_87, A_86]: (r1_xboole_0(B_87, A_86) | k4_xboole_0(A_86, B_87)!=A_86)), inference(resolution, [status(thm)], [c_148, c_12])).
% 27.04/17.08  tff(c_241, plain, (![B_100]: (k3_xboole_0(B_100, B_100)=B_100)), inference(superposition, [status(thm), theory('equality')], [c_206, c_104])).
% 27.04/17.08  tff(c_257, plain, (![B_101]: (~r1_xboole_0(B_101, B_101) | v1_xboole_0(B_101))), inference(superposition, [status(thm), theory('equality')], [c_241, c_204])).
% 27.04/17.08  tff(c_266, plain, (![A_86]: (v1_xboole_0(A_86) | k4_xboole_0(A_86, A_86)!=A_86)), inference(resolution, [status(thm)], [c_155, c_257])).
% 27.04/17.08  tff(c_1082, plain, (![A_167]: (v1_xboole_0(A_167) | k1_xboole_0!=A_167)), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_266])).
% 27.04/17.08  tff(c_175, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_118, c_164])).
% 27.04/17.08  tff(c_197, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_175])).
% 27.04/17.08  tff(c_295, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_278, c_197])).
% 27.04/17.08  tff(c_1106, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_1082, c_295])).
% 27.04/17.08  tff(c_176, plain, ('#skF_5'='#skF_8' | ~r1_tarski('#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_117, c_164])).
% 27.04/17.08  tff(c_196, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_176])).
% 27.04/17.08  tff(c_296, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_278, c_196])).
% 27.04/17.08  tff(c_1105, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_1082, c_296])).
% 27.04/17.08  tff(c_177, plain, ('#skF_6'='#skF_9' | ~r1_tarski('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_116, c_164])).
% 27.04/17.08  tff(c_198, plain, (~r1_tarski('#skF_6', '#skF_9')), inference(splitLeft, [status(thm)], [c_177])).
% 27.04/17.08  tff(c_294, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_278, c_198])).
% 27.04/17.08  tff(c_1107, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_1082, c_294])).
% 27.04/17.08  tff(c_1344, plain, (![A_200, B_201, C_202, D_203]: (k5_mcart_1(A_200, B_201, C_202, D_203)=k1_mcart_1(k1_mcart_1(D_203)) | ~m1_subset_1(D_203, k3_zfmisc_1(A_200, B_201, C_202)) | k1_xboole_0=C_202 | k1_xboole_0=B_201 | k1_xboole_0=A_200)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.08  tff(c_1347, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_1344])).
% 27.04/17.08  tff(c_1350, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_1106, c_1105, c_1107, c_1347])).
% 27.04/17.08  tff(c_901, plain, (![A_156, B_157, C_158]: (k2_zfmisc_1(k2_zfmisc_1(A_156, B_157), C_158)=k3_zfmisc_1(A_156, B_157, C_158))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.08  tff(c_54, plain, (![A_47, B_48, C_49]: (r2_hidden(k1_mcart_1(A_47), B_48) | ~r2_hidden(A_47, k2_zfmisc_1(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.08  tff(c_5919, plain, (![A_417, A_418, B_419, C_420]: (r2_hidden(k1_mcart_1(A_417), k2_zfmisc_1(A_418, B_419)) | ~r2_hidden(A_417, k3_zfmisc_1(A_418, B_419, C_420)))), inference(superposition, [status(thm), theory('equality')], [c_901, c_54])).
% 27.04/17.08  tff(c_5956, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_64, c_5919])).
% 27.04/17.08  tff(c_5972, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_7')), inference(resolution, [status(thm)], [c_5956, c_54])).
% 27.04/17.08  tff(c_5991, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1350, c_5972])).
% 27.04/17.08  tff(c_5993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_5991])).
% 27.04/17.08  tff(c_5994, plain, ('#skF_6'='#skF_9'), inference(splitRight, [status(thm)], [c_177])).
% 27.04/17.08  tff(c_5996, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5994, c_119])).
% 27.04/17.08  tff(c_6189, plain, (![A_446, B_447, C_448]: (~r1_xboole_0(A_446, B_447) | ~r2_hidden(C_448, k3_xboole_0(A_446, B_447)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.04/17.08  tff(c_6235, plain, (![A_453, B_454]: (~r1_xboole_0(A_453, B_454) | v1_xboole_0(k3_xboole_0(A_453, B_454)))), inference(resolution, [status(thm)], [c_4, c_6189])).
% 27.04/17.08  tff(c_6037, plain, (![A_425, B_426]: (r2_hidden('#skF_2'(A_425, B_426), A_425) | r1_tarski(A_425, B_426))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.04/17.08  tff(c_6042, plain, (![A_427, B_428]: (~v1_xboole_0(A_427) | r1_tarski(A_427, B_428))), inference(resolution, [status(thm)], [c_6037, c_2])).
% 27.04/17.08  tff(c_6062, plain, (![A_427]: (k1_xboole_0=A_427 | ~v1_xboole_0(A_427))), inference(resolution, [status(thm)], [c_6042, c_182])).
% 27.04/17.08  tff(c_6331, plain, (![A_467, B_468]: (k3_xboole_0(A_467, B_468)=k1_xboole_0 | ~r1_xboole_0(A_467, B_468))), inference(resolution, [status(thm)], [c_6235, c_6062])).
% 27.04/17.08  tff(c_6358, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_6331])).
% 27.04/17.08  tff(c_6142, plain, (![A_443, B_444]: (k4_xboole_0(A_443, k4_xboole_0(A_443, B_444))=k3_xboole_0(A_443, B_444))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.08  tff(c_6213, plain, (![A_451, B_452]: (r1_xboole_0(k3_xboole_0(A_451, B_452), k4_xboole_0(A_451, B_452)))), inference(superposition, [status(thm), theory('equality')], [c_6142, c_32])).
% 27.04/17.08  tff(c_6274, plain, (![A_460, B_461]: (r1_xboole_0(k4_xboole_0(A_460, B_461), k3_xboole_0(A_460, B_461)))), inference(resolution, [status(thm)], [c_6213, c_12])).
% 27.04/17.08  tff(c_6293, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_6274])).
% 27.04/17.08  tff(c_6392, plain, (![B_471]: (r1_xboole_0(B_471, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6358, c_6293])).
% 27.04/17.08  tff(c_6245, plain, (![A_453, B_454]: (k3_xboole_0(A_453, B_454)=k1_xboole_0 | ~r1_xboole_0(A_453, B_454))), inference(resolution, [status(thm)], [c_6235, c_6062])).
% 27.04/17.08  tff(c_6413, plain, (![B_471]: (k3_xboole_0(B_471, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6392, c_6245])).
% 27.04/17.08  tff(c_6497, plain, (![B_480]: (k4_xboole_0(B_480, k1_xboole_0)=B_480)), inference(resolution, [status(thm)], [c_6392, c_34])).
% 27.04/17.08  tff(c_6515, plain, (![B_480]: (k4_xboole_0(B_480, B_480)=k3_xboole_0(B_480, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6497, c_26])).
% 27.04/17.08  tff(c_6816, plain, (![B_480]: (k4_xboole_0(B_480, B_480)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6413, c_6515])).
% 27.04/17.08  tff(c_6158, plain, (![B_444]: (k3_xboole_0(B_444, B_444)=B_444)), inference(superposition, [status(thm), theory('equality')], [c_6142, c_104])).
% 27.04/17.08  tff(c_6246, plain, (![B_455]: (~r1_xboole_0(B_455, B_455) | v1_xboole_0(B_455))), inference(superposition, [status(thm), theory('equality')], [c_6158, c_6235])).
% 27.04/17.08  tff(c_6255, plain, (![A_86]: (v1_xboole_0(A_86) | k4_xboole_0(A_86, A_86)!=A_86)), inference(resolution, [status(thm)], [c_155, c_6246])).
% 27.04/17.08  tff(c_6817, plain, (![A_86]: (v1_xboole_0(A_86) | k1_xboole_0!=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_6816, c_6255])).
% 27.04/17.08  tff(c_6799, plain, (![C_491, B_492, A_493]: (v1_xboole_0(C_491) | ~m1_subset_1(C_491, k1_zfmisc_1(k2_zfmisc_1(B_492, A_493))) | ~v1_xboole_0(A_493))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.08  tff(c_6806, plain, (![A_32, A_493, B_492]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_493) | ~r2_hidden(A_32, k2_zfmisc_1(B_492, A_493)))), inference(resolution, [status(thm)], [c_40, c_6799])).
% 27.04/17.08  tff(c_7052, plain, (![A_511, A_512, B_513]: (~v1_xboole_0(A_511) | ~r2_hidden(A_512, k2_zfmisc_1(B_513, A_511)))), inference(negUnitSimplification, [status(thm)], [c_38, c_6806])).
% 27.04/17.08  tff(c_7066, plain, (![A_514, B_515]: (~v1_xboole_0(A_514) | v1_xboole_0(k2_zfmisc_1(B_515, A_514)))), inference(resolution, [status(thm)], [c_4, c_7052])).
% 27.04/17.08  tff(c_7402, plain, (![C_549, A_550, B_551]: (~v1_xboole_0(C_549) | v1_xboole_0(k3_zfmisc_1(A_550, B_551, C_549)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_7066])).
% 27.04/17.08  tff(c_7422, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_7402, c_82])).
% 27.04/17.08  tff(c_7426, plain, (k1_xboole_0!='#skF_9'), inference(resolution, [status(thm)], [c_6817, c_7422])).
% 27.04/17.08  tff(c_6883, plain, (![A_495]: (v1_xboole_0(A_495) | k1_xboole_0!=A_495)), inference(demodulation, [status(thm), theory('equality')], [c_6816, c_6255])).
% 27.04/17.08  tff(c_6060, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_6042, c_197])).
% 27.04/17.08  tff(c_6904, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_6883, c_6060])).
% 27.04/17.08  tff(c_6061, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6042, c_196])).
% 27.04/17.08  tff(c_6903, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_6883, c_6061])).
% 27.04/17.08  tff(c_5998, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_5994, c_66])).
% 27.04/17.08  tff(c_7394, plain, (![A_545, B_546, C_547, D_548]: (k5_mcart_1(A_545, B_546, C_547, D_548)=k1_mcart_1(k1_mcart_1(D_548)) | ~m1_subset_1(D_548, k3_zfmisc_1(A_545, B_546, C_547)) | k1_xboole_0=C_547 | k1_xboole_0=B_546 | k1_xboole_0=A_545)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.08  tff(c_7397, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5998, c_7394])).
% 27.04/17.08  tff(c_7400, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_6904, c_6903, c_7397])).
% 27.04/17.08  tff(c_8581, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_7426, c_7400])).
% 27.04/17.08  tff(c_6453, plain, (![A_476, B_477, C_478]: (r2_hidden(k1_mcart_1(A_476), B_477) | ~r2_hidden(A_476, k2_zfmisc_1(B_477, C_478)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.08  tff(c_12866, plain, (![A_788, A_789, B_790, C_791]: (r2_hidden(k1_mcart_1(A_788), k2_zfmisc_1(A_789, B_790)) | ~r2_hidden(A_788, k3_zfmisc_1(A_789, B_790, C_791)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_6453])).
% 27.04/17.08  tff(c_12906, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_64, c_12866])).
% 27.04/17.08  tff(c_12922, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_7')), inference(resolution, [status(thm)], [c_12906, c_54])).
% 27.04/17.08  tff(c_12940, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8581, c_12922])).
% 27.04/17.08  tff(c_12942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5996, c_12940])).
% 27.04/17.08  tff(c_12943, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_175])).
% 27.04/17.08  tff(c_12945, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12943, c_119])).
% 27.04/17.08  tff(c_13090, plain, (![A_810, B_811, C_812]: (~r1_xboole_0(A_810, B_811) | ~r2_hidden(C_812, k3_xboole_0(A_810, B_811)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.04/17.08  tff(c_13102, plain, (![A_815, B_816]: (~r1_xboole_0(A_815, B_816) | v1_xboole_0(k3_xboole_0(A_815, B_816)))), inference(resolution, [status(thm)], [c_4, c_13090])).
% 27.04/17.08  tff(c_12966, plain, (![A_792, B_793]: (r2_hidden('#skF_2'(A_792, B_793), A_792) | r1_tarski(A_792, B_793))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.04/17.08  tff(c_12971, plain, (![A_794, B_795]: (~v1_xboole_0(A_794) | r1_tarski(A_794, B_795))), inference(resolution, [status(thm)], [c_12966, c_2])).
% 27.04/17.08  tff(c_12986, plain, (![A_794]: (k1_xboole_0=A_794 | ~v1_xboole_0(A_794))), inference(resolution, [status(thm)], [c_12971, c_182])).
% 27.04/17.08  tff(c_13110, plain, (![A_817, B_818]: (k3_xboole_0(A_817, B_818)=k1_xboole_0 | ~r1_xboole_0(A_817, B_818))), inference(resolution, [status(thm)], [c_13102, c_12986])).
% 27.04/17.08  tff(c_13125, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_13110])).
% 27.04/17.08  tff(c_13189, plain, (![A_826, B_827]: (k4_xboole_0(A_826, k4_xboole_0(A_826, B_827))=k3_xboole_0(A_826, B_827))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.08  tff(c_13226, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k4_xboole_0(B_28, B_28))), inference(superposition, [status(thm), theory('equality')], [c_104, c_13189])).
% 27.04/17.08  tff(c_13233, plain, (![B_28]: (k4_xboole_0(B_28, B_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_13125, c_13226])).
% 27.04/17.08  tff(c_13243, plain, (![B_831]: (k3_xboole_0(B_831, B_831)=B_831)), inference(superposition, [status(thm), theory('equality')], [c_13189, c_104])).
% 27.04/17.08  tff(c_13100, plain, (![A_810, B_811]: (~r1_xboole_0(A_810, B_811) | v1_xboole_0(k3_xboole_0(A_810, B_811)))), inference(resolution, [status(thm)], [c_4, c_13090])).
% 27.04/17.08  tff(c_13583, plain, (![B_849]: (~r1_xboole_0(B_849, B_849) | v1_xboole_0(B_849))), inference(superposition, [status(thm), theory('equality')], [c_13243, c_13100])).
% 27.04/17.08  tff(c_13595, plain, (![A_86]: (v1_xboole_0(A_86) | k4_xboole_0(A_86, A_86)!=A_86)), inference(resolution, [status(thm)], [c_155, c_13583])).
% 27.04/17.08  tff(c_13610, plain, (![A_850]: (v1_xboole_0(A_850) | k1_xboole_0!=A_850)), inference(demodulation, [status(thm), theory('equality')], [c_13233, c_13595])).
% 27.04/17.08  tff(c_12985, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_12971, c_196])).
% 27.04/17.08  tff(c_13630, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_13610, c_12985])).
% 27.04/17.08  tff(c_12961, plain, (~r1_tarski('#skF_6', '#skF_9')), inference(splitLeft, [status(thm)], [c_177])).
% 27.04/17.08  tff(c_12984, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_12971, c_12961])).
% 27.04/17.08  tff(c_13631, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_13610, c_12984])).
% 27.04/17.08  tff(c_13960, plain, (![A_887, B_888, C_889, D_890]: (k7_mcart_1(A_887, B_888, C_889, D_890)=k2_mcart_1(D_890) | ~m1_subset_1(D_890, k3_zfmisc_1(A_887, B_888, C_889)) | k1_xboole_0=C_889 | k1_xboole_0=B_888 | k1_xboole_0=A_887)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.08  tff(c_13963, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_13960])).
% 27.04/17.08  tff(c_13966, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_13630, c_13631, c_13963])).
% 27.04/17.08  tff(c_14217, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_13966])).
% 27.04/17.08  tff(c_13127, plain, (![B_819, A_820]: (k3_xboole_0(B_819, k4_xboole_0(A_820, B_819))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_13110])).
% 27.04/17.08  tff(c_16, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.04/17.08  tff(c_13135, plain, (![B_819, A_820, C_16]: (~r1_xboole_0(B_819, k4_xboole_0(A_820, B_819)) | ~r2_hidden(C_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_13127, c_16])).
% 27.04/17.08  tff(c_13145, plain, (![C_16]: (~r2_hidden(C_16, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_13135])).
% 27.04/17.08  tff(c_14247, plain, (![C_16]: (~r2_hidden(C_16, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14217, c_13145])).
% 27.04/17.08  tff(c_13605, plain, (![A_86]: (v1_xboole_0(A_86) | k1_xboole_0!=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_13233, c_13595])).
% 27.04/17.08  tff(c_13908, plain, (![C_879, A_880, B_881]: (v1_xboole_0(C_879) | ~m1_subset_1(C_879, k1_zfmisc_1(k2_zfmisc_1(A_880, B_881))) | ~v1_xboole_0(A_880))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.04/17.08  tff(c_13915, plain, (![A_32, A_880, B_881]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_880) | ~r2_hidden(A_32, k2_zfmisc_1(A_880, B_881)))), inference(resolution, [status(thm)], [c_40, c_13908])).
% 27.04/17.08  tff(c_14072, plain, (![A_897, A_898, B_899]: (~v1_xboole_0(A_897) | ~r2_hidden(A_898, k2_zfmisc_1(A_897, B_899)))), inference(negUnitSimplification, [status(thm)], [c_38, c_13915])).
% 27.04/17.08  tff(c_14089, plain, (![A_900, B_901]: (~v1_xboole_0(A_900) | v1_xboole_0(k2_zfmisc_1(A_900, B_901)))), inference(resolution, [status(thm)], [c_4, c_14072])).
% 27.04/17.08  tff(c_14117, plain, (![A_906, B_907]: (k2_zfmisc_1(A_906, B_907)=k1_xboole_0 | ~v1_xboole_0(A_906))), inference(resolution, [status(thm)], [c_14089, c_12986])).
% 27.04/17.08  tff(c_14130, plain, (![A_86, B_907]: (k2_zfmisc_1(A_86, B_907)=k1_xboole_0 | k1_xboole_0!=A_86)), inference(resolution, [status(thm)], [c_13605, c_14117])).
% 27.04/17.08  tff(c_15413, plain, (![B_907]: (k2_zfmisc_1('#skF_4', B_907)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14217, c_14217, c_14130])).
% 27.04/17.08  tff(c_12948, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_12943, c_64])).
% 27.04/17.08  tff(c_13635, plain, (![A_852, B_853, C_854]: (k2_zfmisc_1(k2_zfmisc_1(A_852, B_853), C_854)=k3_zfmisc_1(A_852, B_853, C_854))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.08  tff(c_18367, plain, (![A_1101, A_1102, B_1103, C_1104]: (r2_hidden(k1_mcart_1(A_1101), k2_zfmisc_1(A_1102, B_1103)) | ~r2_hidden(A_1101, k3_zfmisc_1(A_1102, B_1103, C_1104)))), inference(superposition, [status(thm), theory('equality')], [c_13635, c_54])).
% 27.04/17.08  tff(c_18391, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_12948, c_18367])).
% 27.04/17.08  tff(c_18403, plain, (r2_hidden(k1_mcart_1('#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15413, c_18391])).
% 27.04/17.08  tff(c_18405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14247, c_18403])).
% 27.04/17.08  tff(c_18407, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_13966])).
% 27.04/17.08  tff(c_14110, plain, (![A_902, B_903, C_904, D_905]: (k5_mcart_1(A_902, B_903, C_904, D_905)=k1_mcart_1(k1_mcart_1(D_905)) | ~m1_subset_1(D_905, k3_zfmisc_1(A_902, B_903, C_904)) | k1_xboole_0=C_904 | k1_xboole_0=B_903 | k1_xboole_0=A_902)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.08  tff(c_14113, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_14110])).
% 27.04/17.08  tff(c_14116, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_13630, c_13631, c_14113])).
% 27.04/17.08  tff(c_18442, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_18407, c_14116])).
% 27.04/17.08  tff(c_24676, plain, (![A_1353, A_1354, B_1355, C_1356]: (r2_hidden(k1_mcart_1(A_1353), k2_zfmisc_1(A_1354, B_1355)) | ~r2_hidden(A_1353, k3_zfmisc_1(A_1354, B_1355, C_1356)))), inference(superposition, [status(thm), theory('equality')], [c_13635, c_54])).
% 27.04/17.08  tff(c_24719, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_12948, c_24676])).
% 27.04/17.08  tff(c_24736, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_4')), inference(resolution, [status(thm)], [c_24719, c_54])).
% 27.04/17.08  tff(c_24754, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18442, c_24736])).
% 27.04/17.08  tff(c_24756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12945, c_24754])).
% 27.04/17.08  tff(c_24757, plain, ('#skF_6'='#skF_9'), inference(splitRight, [status(thm)], [c_177])).
% 27.04/17.08  tff(c_24777, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24757, c_12945])).
% 27.04/17.08  tff(c_24846, plain, (![A_1364, B_1365, C_1366]: (~r1_xboole_0(A_1364, B_1365) | ~r2_hidden(C_1366, k3_xboole_0(A_1364, B_1365)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.04/17.08  tff(c_24854, plain, (![A_1364, B_1365]: (~r1_xboole_0(A_1364, B_1365) | v1_xboole_0(k3_xboole_0(A_1364, B_1365)))), inference(resolution, [status(thm)], [c_4, c_24846])).
% 27.04/17.08  tff(c_24897, plain, (![A_1378, B_1379]: (r2_hidden('#skF_2'(A_1378, B_1379), A_1378) | r1_tarski(A_1378, B_1379))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.04/17.08  tff(c_24919, plain, (![A_1380, B_1381]: (~v1_xboole_0(A_1380) | r1_tarski(A_1380, B_1381))), inference(resolution, [status(thm)], [c_24897, c_2])).
% 27.04/17.08  tff(c_24932, plain, (![A_1382]: (k1_xboole_0=A_1382 | ~v1_xboole_0(A_1382))), inference(resolution, [status(thm)], [c_24919, c_182])).
% 27.04/17.08  tff(c_25070, plain, (![A_1400, B_1401]: (k3_xboole_0(A_1400, B_1401)=k1_xboole_0 | ~r1_xboole_0(A_1400, B_1401))), inference(resolution, [status(thm)], [c_24854, c_24932])).
% 27.04/17.08  tff(c_25097, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_25070])).
% 27.04/17.08  tff(c_24778, plain, (![A_1357, B_1358]: (k4_xboole_0(A_1357, k4_xboole_0(A_1357, B_1358))=k3_xboole_0(A_1357, B_1358))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.08  tff(c_24828, plain, (![A_1362, B_1363]: (r1_xboole_0(k3_xboole_0(A_1362, B_1363), k4_xboole_0(A_1362, B_1363)))), inference(superposition, [status(thm), theory('equality')], [c_24778, c_32])).
% 27.04/17.08  tff(c_24842, plain, (![B_28, A_27]: (r1_xboole_0(k3_xboole_0(B_28, k4_xboole_0(A_27, B_28)), B_28))), inference(superposition, [status(thm), theory('equality')], [c_104, c_24828])).
% 27.04/17.08  tff(c_25150, plain, (![B_1407]: (r1_xboole_0(k1_xboole_0, B_1407))), inference(demodulation, [status(thm), theory('equality')], [c_25097, c_24842])).
% 27.04/17.08  tff(c_25182, plain, (![B_1408]: (r1_xboole_0(B_1408, k1_xboole_0))), inference(resolution, [status(thm)], [c_25150, c_12])).
% 27.04/17.08  tff(c_24939, plain, (![A_1364, B_1365]: (k3_xboole_0(A_1364, B_1365)=k1_xboole_0 | ~r1_xboole_0(A_1364, B_1365))), inference(resolution, [status(thm)], [c_24854, c_24932])).
% 27.04/17.08  tff(c_25205, plain, (![B_1408]: (k3_xboole_0(B_1408, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_25182, c_24939])).
% 27.04/17.08  tff(c_25239, plain, (![B_1411]: (k4_xboole_0(k1_xboole_0, B_1411)=k1_xboole_0)), inference(resolution, [status(thm)], [c_25150, c_34])).
% 27.04/17.08  tff(c_25359, plain, (![B_1416]: (k4_xboole_0(B_1416, k1_xboole_0)=B_1416)), inference(superposition, [status(thm), theory('equality')], [c_25239, c_104])).
% 27.04/17.08  tff(c_25384, plain, (![B_1416]: (k4_xboole_0(B_1416, B_1416)=k3_xboole_0(B_1416, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_25359, c_26])).
% 27.04/17.08  tff(c_25682, plain, (![B_1416]: (k4_xboole_0(B_1416, B_1416)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_25205, c_25384])).
% 27.04/17.08  tff(c_24791, plain, (![B_1358]: (k3_xboole_0(B_1358, B_1358)=B_1358)), inference(superposition, [status(thm), theory('equality')], [c_24778, c_104])).
% 27.04/17.08  tff(c_24881, plain, (![A_1374, B_1375]: (~r1_xboole_0(A_1374, B_1375) | v1_xboole_0(k3_xboole_0(A_1374, B_1375)))), inference(resolution, [status(thm)], [c_4, c_24846])).
% 27.04/17.08  tff(c_24885, plain, (![B_1376]: (~r1_xboole_0(B_1376, B_1376) | v1_xboole_0(B_1376))), inference(superposition, [status(thm), theory('equality')], [c_24791, c_24881])).
% 27.04/17.08  tff(c_24894, plain, (![A_86]: (v1_xboole_0(A_86) | k4_xboole_0(A_86, A_86)!=A_86)), inference(resolution, [status(thm)], [c_155, c_24885])).
% 27.04/17.08  tff(c_25749, plain, (![A_1439]: (v1_xboole_0(A_1439) | k1_xboole_0!=A_1439)), inference(demodulation, [status(thm), theory('equality')], [c_25682, c_24894])).
% 27.04/17.08  tff(c_24929, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_24919, c_196])).
% 27.04/17.08  tff(c_25766, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_25749, c_24929])).
% 27.04/17.08  tff(c_24760, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_24757, c_66])).
% 27.04/17.08  tff(c_25850, plain, (![A_1455, B_1456, C_1457, D_1458]: (k7_mcart_1(A_1455, B_1456, C_1457, D_1458)=k2_mcart_1(D_1458) | ~m1_subset_1(D_1458, k3_zfmisc_1(A_1455, B_1456, C_1457)) | k1_xboole_0=C_1457 | k1_xboole_0=B_1456 | k1_xboole_0=A_1455)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.08  tff(c_25853, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_24760, c_25850])).
% 27.04/17.08  tff(c_25856, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_25766, c_25853])).
% 27.04/17.08  tff(c_26079, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_25856])).
% 27.04/17.08  tff(c_25683, plain, (![A_86]: (v1_xboole_0(A_86) | k1_xboole_0!=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_25682, c_24894])).
% 27.04/17.08  tff(c_26561, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26079, c_25683])).
% 27.04/17.08  tff(c_25472, plain, (![A_1421, B_1422, C_1423]: (r2_hidden(k1_mcart_1(A_1421), B_1422) | ~r2_hidden(A_1421, k2_zfmisc_1(B_1422, C_1423)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.08  tff(c_29319, plain, (![B_1643, C_1644]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1643, C_1644))), B_1643) | v1_xboole_0(k2_zfmisc_1(B_1643, C_1644)))), inference(resolution, [status(thm)], [c_4, c_25472])).
% 27.04/17.08  tff(c_25801, plain, (![C_1445, A_1446, B_1447]: (v1_xboole_0(C_1445) | ~m1_subset_1(C_1445, k1_zfmisc_1(k2_zfmisc_1(A_1446, B_1447))) | ~v1_xboole_0(A_1446))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.04/17.08  tff(c_25808, plain, (![A_32, A_1446, B_1447]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_1446) | ~r2_hidden(A_32, k2_zfmisc_1(A_1446, B_1447)))), inference(resolution, [status(thm)], [c_40, c_25801])).
% 27.04/17.08  tff(c_25815, plain, (![A_1446, A_32, B_1447]: (~v1_xboole_0(A_1446) | ~r2_hidden(A_32, k2_zfmisc_1(A_1446, B_1447)))), inference(negUnitSimplification, [status(thm)], [c_38, c_25808])).
% 27.04/17.08  tff(c_29336, plain, (![A_1446, B_1447, C_1644]: (~v1_xboole_0(A_1446) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_1446, B_1447), C_1644)))), inference(resolution, [status(thm)], [c_29319, c_25815])).
% 27.04/17.08  tff(c_29736, plain, (![A_1659, B_1660, C_1661]: (~v1_xboole_0(A_1659) | v1_xboole_0(k3_zfmisc_1(A_1659, B_1660, C_1661)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_29336])).
% 27.04/17.08  tff(c_12947, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_12943, c_82])).
% 27.04/17.08  tff(c_29764, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_29736, c_12947])).
% 27.04/17.08  tff(c_29783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26561, c_29764])).
% 27.04/17.08  tff(c_29785, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_25856])).
% 27.04/17.08  tff(c_25508, plain, (![C_1425, B_1426, A_1427]: (v1_xboole_0(C_1425) | ~m1_subset_1(C_1425, k1_zfmisc_1(k2_zfmisc_1(B_1426, A_1427))) | ~v1_xboole_0(A_1427))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.08  tff(c_25515, plain, (![A_32, A_1427, B_1426]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_1427) | ~r2_hidden(A_32, k2_zfmisc_1(B_1426, A_1427)))), inference(resolution, [status(thm)], [c_40, c_25508])).
% 27.04/17.08  tff(c_25822, plain, (![A_1450, A_1451, B_1452]: (~v1_xboole_0(A_1450) | ~r2_hidden(A_1451, k2_zfmisc_1(B_1452, A_1450)))), inference(negUnitSimplification, [status(thm)], [c_38, c_25515])).
% 27.04/17.08  tff(c_25836, plain, (![A_1453, B_1454]: (~v1_xboole_0(A_1453) | v1_xboole_0(k2_zfmisc_1(B_1454, A_1453)))), inference(resolution, [status(thm)], [c_4, c_25822])).
% 27.04/17.08  tff(c_29862, plain, (![C_1668, A_1669, B_1670]: (~v1_xboole_0(C_1668) | v1_xboole_0(k3_zfmisc_1(A_1669, B_1670, C_1668)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_25836])).
% 27.04/17.08  tff(c_29882, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_29862, c_12947])).
% 27.04/17.08  tff(c_29893, plain, (k1_xboole_0!='#skF_9'), inference(resolution, [status(thm)], [c_25683, c_29882])).
% 27.04/17.08  tff(c_25983, plain, (![A_1469, B_1470, C_1471, D_1472]: (k5_mcart_1(A_1469, B_1470, C_1471, D_1472)=k1_mcart_1(k1_mcart_1(D_1472)) | ~m1_subset_1(D_1472, k3_zfmisc_1(A_1469, B_1470, C_1471)) | k1_xboole_0=C_1471 | k1_xboole_0=B_1470 | k1_xboole_0=A_1469)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.08  tff(c_25986, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_24760, c_25983])).
% 27.04/17.08  tff(c_25989, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_25766, c_25986])).
% 27.04/17.08  tff(c_30123, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_29785, c_29893, c_25989])).
% 27.04/17.08  tff(c_35242, plain, (![A_1916, A_1917, B_1918, C_1919]: (r2_hidden(k1_mcart_1(A_1916), k2_zfmisc_1(A_1917, B_1918)) | ~r2_hidden(A_1916, k3_zfmisc_1(A_1917, B_1918, C_1919)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_25472])).
% 27.04/17.08  tff(c_35285, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_12948, c_35242])).
% 27.04/17.08  tff(c_35300, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_4')), inference(resolution, [status(thm)], [c_35285, c_54])).
% 27.04/17.08  tff(c_35319, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30123, c_35300])).
% 27.04/17.08  tff(c_35321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24777, c_35319])).
% 27.04/17.08  tff(c_35322, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_176])).
% 27.04/17.08  tff(c_35324, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_35322, c_119])).
% 27.04/17.08  tff(c_35536, plain, (![A_1945, B_1946, C_1947]: (~r1_xboole_0(A_1945, B_1946) | ~r2_hidden(C_1947, k3_xboole_0(A_1945, B_1946)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.04/17.08  tff(c_35559, plain, (![A_1950, B_1951]: (~r1_xboole_0(A_1950, B_1951) | v1_xboole_0(k3_xboole_0(A_1950, B_1951)))), inference(resolution, [status(thm)], [c_4, c_35536])).
% 27.04/17.08  tff(c_35362, plain, (![A_1925, B_1926]: (r2_hidden('#skF_2'(A_1925, B_1926), A_1925) | r1_tarski(A_1925, B_1926))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.04/17.08  tff(c_35373, plain, (![A_1927, B_1928]: (~v1_xboole_0(A_1927) | r1_tarski(A_1927, B_1928))), inference(resolution, [status(thm)], [c_35362, c_2])).
% 27.04/17.08  tff(c_35388, plain, (![A_1927]: (k1_xboole_0=A_1927 | ~v1_xboole_0(A_1927))), inference(resolution, [status(thm)], [c_35373, c_182])).
% 27.04/17.08  tff(c_35613, plain, (![A_1958, B_1959]: (k3_xboole_0(A_1958, B_1959)=k1_xboole_0 | ~r1_xboole_0(A_1958, B_1959))), inference(resolution, [status(thm)], [c_35559, c_35388])).
% 27.04/17.08  tff(c_35657, plain, (![B_1963, A_1964]: (k3_xboole_0(B_1963, k4_xboole_0(A_1964, B_1963))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_35613])).
% 27.04/17.08  tff(c_35443, plain, (![A_1936, B_1937]: (k4_xboole_0(A_1936, k4_xboole_0(A_1936, B_1937))=k3_xboole_0(A_1936, B_1937))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.09  tff(c_35488, plain, (![A_1939, B_1940]: (r1_xboole_0(k3_xboole_0(A_1939, B_1940), k4_xboole_0(A_1939, B_1940)))), inference(superposition, [status(thm), theory('equality')], [c_35443, c_32])).
% 27.04/17.09  tff(c_35508, plain, (![A_1939, B_1940]: (r1_xboole_0(k4_xboole_0(A_1939, B_1940), k3_xboole_0(A_1939, B_1940)))), inference(resolution, [status(thm)], [c_35488, c_12])).
% 27.04/17.09  tff(c_35662, plain, (![B_1963, A_1964]: (r1_xboole_0(k4_xboole_0(B_1963, k4_xboole_0(A_1964, B_1963)), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_35657, c_35508])).
% 27.04/17.09  tff(c_35688, plain, (![B_1965]: (r1_xboole_0(B_1965, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_35662])).
% 27.04/17.09  tff(c_35569, plain, (![A_1950, B_1951]: (k3_xboole_0(A_1950, B_1951)=k1_xboole_0 | ~r1_xboole_0(A_1950, B_1951))), inference(resolution, [status(thm)], [c_35559, c_35388])).
% 27.04/17.09  tff(c_35711, plain, (![B_1965]: (k3_xboole_0(B_1965, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_35688, c_35569])).
% 27.04/17.09  tff(c_35774, plain, (![B_1971]: (k4_xboole_0(B_1971, k1_xboole_0)=B_1971)), inference(resolution, [status(thm)], [c_35688, c_34])).
% 27.04/17.09  tff(c_35795, plain, (![B_1971]: (k4_xboole_0(B_1971, B_1971)=k3_xboole_0(B_1971, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_35774, c_26])).
% 27.04/17.09  tff(c_36132, plain, (![B_1971]: (k4_xboole_0(B_1971, B_1971)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_35711, c_35795])).
% 27.04/17.09  tff(c_35456, plain, (![B_1937]: (k3_xboole_0(B_1937, B_1937)=B_1937)), inference(superposition, [status(thm), theory('equality')], [c_35443, c_104])).
% 27.04/17.09  tff(c_35570, plain, (![B_1952]: (~r1_xboole_0(B_1952, B_1952) | v1_xboole_0(B_1952))), inference(superposition, [status(thm), theory('equality')], [c_35456, c_35559])).
% 27.04/17.09  tff(c_35580, plain, (![B_30]: (v1_xboole_0(B_30) | k4_xboole_0(B_30, B_30)!=B_30)), inference(resolution, [status(thm)], [c_36, c_35570])).
% 27.04/17.09  tff(c_36199, plain, (![B_1991]: (v1_xboole_0(B_1991) | k1_xboole_0!=B_1991)), inference(demodulation, [status(thm), theory('equality')], [c_36132, c_35580])).
% 27.04/17.09  tff(c_35340, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_175])).
% 27.04/17.09  tff(c_35386, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_35373, c_35340])).
% 27.04/17.09  tff(c_36220, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_36199, c_35386])).
% 27.04/17.09  tff(c_35339, plain, (~r1_tarski('#skF_6', '#skF_9')), inference(splitLeft, [status(thm)], [c_177])).
% 27.04/17.09  tff(c_35387, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_35373, c_35339])).
% 27.04/17.09  tff(c_36219, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_36199, c_35387])).
% 27.04/17.09  tff(c_35326, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_35322, c_66])).
% 27.04/17.09  tff(c_36562, plain, (![A_2030, B_2031, C_2032, D_2033]: (k7_mcart_1(A_2030, B_2031, C_2032, D_2033)=k2_mcart_1(D_2033) | ~m1_subset_1(D_2033, k3_zfmisc_1(A_2030, B_2031, C_2032)) | k1_xboole_0=C_2032 | k1_xboole_0=B_2031 | k1_xboole_0=A_2030)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_36565, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_35326, c_36562])).
% 27.04/17.09  tff(c_36568, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_36220, c_36219, c_36565])).
% 27.04/17.09  tff(c_36698, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_36568])).
% 27.04/17.09  tff(c_36133, plain, (![B_30]: (v1_xboole_0(B_30) | k1_xboole_0!=B_30)), inference(demodulation, [status(thm), theory('equality')], [c_36132, c_35580])).
% 27.04/17.09  tff(c_36714, plain, (![B_30]: (v1_xboole_0(B_30) | B_30!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36698, c_36133])).
% 27.04/17.09  tff(c_36372, plain, (![C_2007, B_2008, A_2009]: (v1_xboole_0(C_2007) | ~m1_subset_1(C_2007, k1_zfmisc_1(k2_zfmisc_1(B_2008, A_2009))) | ~v1_xboole_0(A_2009))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.09  tff(c_36379, plain, (![A_32, A_2009, B_2008]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_2009) | ~r2_hidden(A_32, k2_zfmisc_1(B_2008, A_2009)))), inference(resolution, [status(thm)], [c_40, c_36372])).
% 27.04/17.09  tff(c_36418, plain, (![A_2011, A_2012, B_2013]: (~v1_xboole_0(A_2011) | ~r2_hidden(A_2012, k2_zfmisc_1(B_2013, A_2011)))), inference(negUnitSimplification, [status(thm)], [c_38, c_36379])).
% 27.04/17.09  tff(c_36431, plain, (![A_2011, B_2013]: (~v1_xboole_0(A_2011) | v1_xboole_0(k2_zfmisc_1(B_2013, A_2011)))), inference(resolution, [status(thm)], [c_4, c_36418])).
% 27.04/17.09  tff(c_36446, plain, (![C_2016, A_2017, B_2018]: (v1_xboole_0(C_2016) | ~m1_subset_1(C_2016, k1_zfmisc_1(k2_zfmisc_1(A_2017, B_2018))) | ~v1_xboole_0(A_2017))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.04/17.09  tff(c_36453, plain, (![A_32, A_2017, B_2018]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_2017) | ~r2_hidden(A_32, k2_zfmisc_1(A_2017, B_2018)))), inference(resolution, [status(thm)], [c_40, c_36446])).
% 27.04/17.09  tff(c_36509, plain, (![A_2023, A_2024, B_2025]: (~v1_xboole_0(A_2023) | ~r2_hidden(A_2024, k2_zfmisc_1(A_2023, B_2025)))), inference(negUnitSimplification, [status(thm)], [c_38, c_36453])).
% 27.04/17.09  tff(c_36526, plain, (![A_2026, B_2027]: (~v1_xboole_0(A_2026) | v1_xboole_0(k2_zfmisc_1(A_2026, B_2027)))), inference(resolution, [status(thm)], [c_4, c_36509])).
% 27.04/17.09  tff(c_36547, plain, (![A_2028, B_2029]: (k2_zfmisc_1(A_2028, B_2029)=k1_xboole_0 | ~v1_xboole_0(A_2028))), inference(resolution, [status(thm)], [c_36526, c_35388])).
% 27.04/17.09  tff(c_36551, plain, (![B_2013, A_2011, B_2029]: (k2_zfmisc_1(k2_zfmisc_1(B_2013, A_2011), B_2029)=k1_xboole_0 | ~v1_xboole_0(A_2011))), inference(resolution, [status(thm)], [c_36431, c_36547])).
% 27.04/17.09  tff(c_36559, plain, (![B_2013, A_2011, B_2029]: (k3_zfmisc_1(B_2013, A_2011, B_2029)=k1_xboole_0 | ~v1_xboole_0(A_2011))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_36551])).
% 27.04/17.09  tff(c_39060, plain, (![B_2161, A_2162, B_2163]: (k3_zfmisc_1(B_2161, A_2162, B_2163)='#skF_8' | ~v1_xboole_0(A_2162))), inference(demodulation, [status(thm), theory('equality')], [c_36698, c_36559])).
% 27.04/17.09  tff(c_40074, plain, (![B_2161, B_2163]: (k3_zfmisc_1(B_2161, '#skF_8', B_2163)='#skF_8')), inference(resolution, [status(thm)], [c_36714, c_39060])).
% 27.04/17.09  tff(c_36221, plain, (k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_36199, c_82])).
% 27.04/17.09  tff(c_36710, plain, (k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36698, c_36221])).
% 27.04/17.09  tff(c_40082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40074, c_36710])).
% 27.04/17.09  tff(c_40084, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_36568])).
% 27.04/17.09  tff(c_40283, plain, (![A_2242, B_2243, C_2244, D_2245]: (k5_mcart_1(A_2242, B_2243, C_2244, D_2245)=k1_mcart_1(k1_mcart_1(D_2245)) | ~m1_subset_1(D_2245, k3_zfmisc_1(A_2242, B_2243, C_2244)) | k1_xboole_0=C_2244 | k1_xboole_0=B_2243 | k1_xboole_0=A_2242)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_40286, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_35326, c_40283])).
% 27.04/17.09  tff(c_40289, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_36220, c_40084, c_36219, c_40286])).
% 27.04/17.09  tff(c_36121, plain, (![A_1987, B_1988, C_1989]: (r2_hidden(k1_mcart_1(A_1987), B_1988) | ~r2_hidden(A_1987, k2_zfmisc_1(B_1988, C_1989)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_45897, plain, (![A_2471, A_2472, B_2473, C_2474]: (r2_hidden(k1_mcart_1(A_2471), k2_zfmisc_1(A_2472, B_2473)) | ~r2_hidden(A_2471, k3_zfmisc_1(A_2472, B_2473, C_2474)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_36121])).
% 27.04/17.09  tff(c_45941, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_64, c_45897])).
% 27.04/17.09  tff(c_46017, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_7')), inference(resolution, [status(thm)], [c_45941, c_54])).
% 27.04/17.09  tff(c_46036, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40289, c_46017])).
% 27.04/17.09  tff(c_46038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35324, c_46036])).
% 27.04/17.09  tff(c_46039, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_175])).
% 27.04/17.09  tff(c_46086, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46039, c_35324])).
% 27.04/17.09  tff(c_46316, plain, (![A_2510, B_2511, C_2512]: (~r1_xboole_0(A_2510, B_2511) | ~r2_hidden(C_2512, k3_xboole_0(A_2510, B_2511)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.04/17.09  tff(c_46339, plain, (![A_2515, B_2516]: (~r1_xboole_0(A_2515, B_2516) | v1_xboole_0(k3_xboole_0(A_2515, B_2516)))), inference(resolution, [status(thm)], [c_4, c_46316])).
% 27.04/17.09  tff(c_46210, plain, (![A_2495, B_2496]: (r2_hidden('#skF_2'(A_2495, B_2496), A_2495) | r1_tarski(A_2495, B_2496))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.04/17.09  tff(c_46221, plain, (![A_2497, B_2498]: (~v1_xboole_0(A_2497) | r1_tarski(A_2497, B_2498))), inference(resolution, [status(thm)], [c_46210, c_2])).
% 27.04/17.09  tff(c_46237, plain, (![A_2497]: (k1_xboole_0=A_2497 | ~v1_xboole_0(A_2497))), inference(resolution, [status(thm)], [c_46221, c_182])).
% 27.04/17.09  tff(c_46372, plain, (![A_2522, B_2523]: (k3_xboole_0(A_2522, B_2523)=k1_xboole_0 | ~r1_xboole_0(A_2522, B_2523))), inference(resolution, [status(thm)], [c_46339, c_46237])).
% 27.04/17.09  tff(c_46403, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_46372])).
% 27.04/17.09  tff(c_46087, plain, (![A_2481, B_2482]: (k4_xboole_0(A_2481, k4_xboole_0(A_2481, B_2482))=k3_xboole_0(A_2481, B_2482))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.09  tff(c_46157, plain, (![A_2486, B_2487]: (r1_xboole_0(k4_xboole_0(A_2486, B_2487), k3_xboole_0(A_2486, B_2487)))), inference(superposition, [status(thm), theory('equality')], [c_46087, c_91])).
% 27.04/17.09  tff(c_46174, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_46157])).
% 27.04/17.09  tff(c_46438, plain, (![B_2526]: (r1_xboole_0(B_2526, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46403, c_46174])).
% 27.04/17.09  tff(c_46349, plain, (![A_2515, B_2516]: (k3_xboole_0(A_2515, B_2516)=k1_xboole_0 | ~r1_xboole_0(A_2515, B_2516))), inference(resolution, [status(thm)], [c_46339, c_46237])).
% 27.04/17.09  tff(c_46457, plain, (![B_2526]: (k3_xboole_0(B_2526, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_46438, c_46349])).
% 27.04/17.09  tff(c_46590, plain, (![B_2537]: (k4_xboole_0(B_2537, k1_xboole_0)=B_2537)), inference(resolution, [status(thm)], [c_46438, c_34])).
% 27.04/17.09  tff(c_46608, plain, (![B_2537]: (k4_xboole_0(B_2537, B_2537)=k3_xboole_0(B_2537, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46590, c_26])).
% 27.04/17.09  tff(c_46893, plain, (![B_2537]: (k4_xboole_0(B_2537, B_2537)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46457, c_46608])).
% 27.04/17.09  tff(c_46103, plain, (![B_2482]: (k3_xboole_0(B_2482, B_2482)=B_2482)), inference(superposition, [status(thm), theory('equality')], [c_46087, c_104])).
% 27.04/17.09  tff(c_46350, plain, (![B_2517]: (~r1_xboole_0(B_2517, B_2517) | v1_xboole_0(B_2517))), inference(superposition, [status(thm), theory('equality')], [c_46103, c_46339])).
% 27.04/17.09  tff(c_46359, plain, (![A_86]: (v1_xboole_0(A_86) | k4_xboole_0(A_86, A_86)!=A_86)), inference(resolution, [status(thm)], [c_155, c_46350])).
% 27.04/17.09  tff(c_46976, plain, (![A_2555]: (v1_xboole_0(A_2555) | k1_xboole_0!=A_2555)), inference(demodulation, [status(thm), theory('equality')], [c_46893, c_46359])).
% 27.04/17.09  tff(c_46236, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_46221, c_35339])).
% 27.04/17.09  tff(c_46993, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_46976, c_46236])).
% 27.04/17.09  tff(c_47257, plain, (![A_2588, B_2589, C_2590, D_2591]: (k7_mcart_1(A_2588, B_2589, C_2590, D_2591)=k2_mcart_1(D_2591) | ~m1_subset_1(D_2591, k3_zfmisc_1(A_2588, B_2589, C_2590)) | k1_xboole_0=C_2590 | k1_xboole_0=B_2589 | k1_xboole_0=A_2588)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_47260, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_35326, c_47257])).
% 27.04/17.09  tff(c_47263, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46993, c_47260])).
% 27.04/17.09  tff(c_47379, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_47263])).
% 27.04/17.09  tff(c_46894, plain, (![A_86]: (v1_xboole_0(A_86) | k1_xboole_0!=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_46893, c_46359])).
% 27.04/17.09  tff(c_47813, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47379, c_46894])).
% 27.04/17.09  tff(c_46753, plain, (![A_2540, B_2541, C_2542]: (r2_hidden(k1_mcart_1(A_2540), B_2541) | ~r2_hidden(A_2540, k2_zfmisc_1(B_2541, C_2542)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_50975, plain, (![B_2778, C_2779]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2778, C_2779))), B_2778) | v1_xboole_0(k2_zfmisc_1(B_2778, C_2779)))), inference(resolution, [status(thm)], [c_4, c_46753])).
% 27.04/17.09  tff(c_47069, plain, (![C_2565, A_2566, B_2567]: (v1_xboole_0(C_2565) | ~m1_subset_1(C_2565, k1_zfmisc_1(k2_zfmisc_1(A_2566, B_2567))) | ~v1_xboole_0(A_2566))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.04/17.09  tff(c_47076, plain, (![A_32, A_2566, B_2567]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_2566) | ~r2_hidden(A_32, k2_zfmisc_1(A_2566, B_2567)))), inference(resolution, [status(thm)], [c_40, c_47069])).
% 27.04/17.09  tff(c_47083, plain, (![A_2566, A_32, B_2567]: (~v1_xboole_0(A_2566) | ~r2_hidden(A_32, k2_zfmisc_1(A_2566, B_2567)))), inference(negUnitSimplification, [status(thm)], [c_38, c_47076])).
% 27.04/17.09  tff(c_50992, plain, (![A_2566, B_2567, C_2779]: (~v1_xboole_0(A_2566) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_2566, B_2567), C_2779)))), inference(resolution, [status(thm)], [c_50975, c_47083])).
% 27.04/17.09  tff(c_51089, plain, (![A_2782, B_2783, C_2784]: (~v1_xboole_0(A_2782) | v1_xboole_0(k3_zfmisc_1(A_2782, B_2783, C_2784)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50992])).
% 27.04/17.09  tff(c_46042, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_46039, c_82])).
% 27.04/17.09  tff(c_51117, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_51089, c_46042])).
% 27.04/17.09  tff(c_51133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47813, c_51117])).
% 27.04/17.09  tff(c_51135, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_47263])).
% 27.04/17.09  tff(c_51238, plain, (![A_2794, B_2795, C_2796, D_2797]: (k5_mcart_1(A_2794, B_2795, C_2796, D_2797)=k1_mcart_1(k1_mcart_1(D_2797)) | ~m1_subset_1(D_2797, k3_zfmisc_1(A_2794, B_2795, C_2796)) | k1_xboole_0=C_2796 | k1_xboole_0=B_2795 | k1_xboole_0=A_2794)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_51241, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_35326, c_51238])).
% 27.04/17.09  tff(c_51244, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_51135, c_46993, c_51241])).
% 27.04/17.09  tff(c_51281, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_51244])).
% 27.04/17.09  tff(c_51818, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_51281, c_46894])).
% 27.04/17.09  tff(c_54182, plain, (![B_2945, C_2946]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2945, C_2946))), B_2945) | v1_xboole_0(k2_zfmisc_1(B_2945, C_2946)))), inference(resolution, [status(thm)], [c_4, c_46753])).
% 27.04/17.09  tff(c_46958, plain, (![C_2552, B_2553, A_2554]: (v1_xboole_0(C_2552) | ~m1_subset_1(C_2552, k1_zfmisc_1(k2_zfmisc_1(B_2553, A_2554))) | ~v1_xboole_0(A_2554))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.09  tff(c_46965, plain, (![A_32, A_2554, B_2553]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_2554) | ~r2_hidden(A_32, k2_zfmisc_1(B_2553, A_2554)))), inference(resolution, [status(thm)], [c_40, c_46958])).
% 27.04/17.09  tff(c_46972, plain, (![A_2554, A_32, B_2553]: (~v1_xboole_0(A_2554) | ~r2_hidden(A_32, k2_zfmisc_1(B_2553, A_2554)))), inference(negUnitSimplification, [status(thm)], [c_38, c_46965])).
% 27.04/17.09  tff(c_54203, plain, (![A_2554, B_2553, C_2946]: (~v1_xboole_0(A_2554) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_2553, A_2554), C_2946)))), inference(resolution, [status(thm)], [c_54182, c_46972])).
% 27.04/17.09  tff(c_54845, plain, (![A_2967, B_2968, C_2969]: (~v1_xboole_0(A_2967) | v1_xboole_0(k3_zfmisc_1(B_2968, A_2967, C_2969)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_54203])).
% 27.04/17.09  tff(c_54873, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_54845, c_46042])).
% 27.04/17.09  tff(c_54889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51818, c_54873])).
% 27.04/17.09  tff(c_54890, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_51244])).
% 27.04/17.09  tff(c_46043, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_46039, c_64])).
% 27.04/17.09  tff(c_60895, plain, (![A_3216, A_3217, B_3218, C_3219]: (r2_hidden(k1_mcart_1(A_3216), k2_zfmisc_1(A_3217, B_3218)) | ~r2_hidden(A_3216, k3_zfmisc_1(A_3217, B_3218, C_3219)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_46753])).
% 27.04/17.09  tff(c_60938, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_46043, c_60895])).
% 27.04/17.09  tff(c_60953, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_4')), inference(resolution, [status(thm)], [c_60938, c_54])).
% 27.04/17.09  tff(c_60972, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54890, c_60953])).
% 27.04/17.09  tff(c_60974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46086, c_60972])).
% 27.04/17.09  tff(c_60975, plain, ('#skF_6'='#skF_9'), inference(splitRight, [status(thm)], [c_177])).
% 27.04/17.09  tff(c_60992, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60975, c_35324])).
% 27.04/17.09  tff(c_61020, plain, (![A_3226, B_3227, C_3228]: (~r1_xboole_0(A_3226, B_3227) | ~r2_hidden(C_3228, k3_xboole_0(A_3226, B_3227)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.04/17.09  tff(c_61025, plain, (![A_3226, B_3227]: (~r1_xboole_0(A_3226, B_3227) | v1_xboole_0(k3_xboole_0(A_3226, B_3227)))), inference(resolution, [status(thm)], [c_4, c_61020])).
% 27.04/17.09  tff(c_61094, plain, (![A_3240, B_3241]: (r2_hidden('#skF_2'(A_3240, B_3241), A_3240) | r1_tarski(A_3240, B_3241))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.04/17.09  tff(c_61132, plain, (![A_3243, B_3244]: (~v1_xboole_0(A_3243) | r1_tarski(A_3243, B_3244))), inference(resolution, [status(thm)], [c_61094, c_2])).
% 27.04/17.09  tff(c_61150, plain, (![A_3245]: (k1_xboole_0=A_3245 | ~v1_xboole_0(A_3245))), inference(resolution, [status(thm)], [c_61132, c_182])).
% 27.04/17.09  tff(c_61282, plain, (![A_3264, B_3265]: (k3_xboole_0(A_3264, B_3265)=k1_xboole_0 | ~r1_xboole_0(A_3264, B_3265))), inference(resolution, [status(thm)], [c_61025, c_61150])).
% 27.04/17.09  tff(c_61307, plain, (![B_3266, A_3267]: (k3_xboole_0(B_3266, k4_xboole_0(A_3267, B_3266))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_61282])).
% 27.04/17.09  tff(c_61056, plain, (![A_3238, B_3239]: (k4_xboole_0(A_3238, k4_xboole_0(A_3238, B_3239))=k3_xboole_0(A_3238, B_3239))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.09  tff(c_61190, plain, (![A_3253, B_3254]: (r1_xboole_0(k3_xboole_0(A_3253, B_3254), k4_xboole_0(A_3253, B_3254)))), inference(superposition, [status(thm), theory('equality')], [c_61056, c_32])).
% 27.04/17.09  tff(c_61210, plain, (![A_3253, B_3254]: (r1_xboole_0(k4_xboole_0(A_3253, B_3254), k3_xboole_0(A_3253, B_3254)))), inference(resolution, [status(thm)], [c_61190, c_12])).
% 27.04/17.09  tff(c_61312, plain, (![B_3266, A_3267]: (r1_xboole_0(k4_xboole_0(B_3266, k4_xboole_0(A_3267, B_3266)), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_61307, c_61210])).
% 27.04/17.09  tff(c_61338, plain, (![B_3268]: (r1_xboole_0(B_3268, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_61312])).
% 27.04/17.09  tff(c_61157, plain, (![A_3226, B_3227]: (k3_xboole_0(A_3226, B_3227)=k1_xboole_0 | ~r1_xboole_0(A_3226, B_3227))), inference(resolution, [status(thm)], [c_61025, c_61150])).
% 27.04/17.09  tff(c_61357, plain, (![B_3268]: (k3_xboole_0(B_3268, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_61338, c_61157])).
% 27.04/17.09  tff(c_61428, plain, (![B_3277]: (k4_xboole_0(B_3277, k1_xboole_0)=B_3277)), inference(resolution, [status(thm)], [c_61338, c_34])).
% 27.04/17.09  tff(c_61446, plain, (![B_3277]: (k4_xboole_0(B_3277, B_3277)=k3_xboole_0(B_3277, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_61428, c_26])).
% 27.04/17.09  tff(c_61827, plain, (![B_3277]: (k4_xboole_0(B_3277, B_3277)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61357, c_61446])).
% 27.04/17.09  tff(c_61116, plain, (![B_3242]: (k3_xboole_0(B_3242, B_3242)=B_3242)), inference(superposition, [status(thm), theory('equality')], [c_61056, c_104])).
% 27.04/17.09  tff(c_61160, plain, (![B_3246]: (~r1_xboole_0(B_3246, B_3246) | v1_xboole_0(B_3246))), inference(superposition, [status(thm), theory('equality')], [c_61116, c_61025])).
% 27.04/17.09  tff(c_61169, plain, (![A_86]: (v1_xboole_0(A_86) | k4_xboole_0(A_86, A_86)!=A_86)), inference(resolution, [status(thm)], [c_155, c_61160])).
% 27.04/17.09  tff(c_61894, plain, (![A_3296]: (v1_xboole_0(A_3296) | k1_xboole_0!=A_3296)), inference(demodulation, [status(thm), theory('equality')], [c_61827, c_61169])).
% 27.04/17.09  tff(c_60990, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_175])).
% 27.04/17.09  tff(c_61147, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_61132, c_60990])).
% 27.04/17.09  tff(c_61911, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_61894, c_61147])).
% 27.04/17.09  tff(c_60991, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60975, c_35326])).
% 27.04/17.09  tff(c_61931, plain, (![A_3301, B_3302, C_3303, D_3304]: (k7_mcart_1(A_3301, B_3302, C_3303, D_3304)=k2_mcart_1(D_3304) | ~m1_subset_1(D_3304, k3_zfmisc_1(A_3301, B_3302, C_3303)) | k1_xboole_0=C_3303 | k1_xboole_0=B_3302 | k1_xboole_0=A_3301)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_61934, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60991, c_61931])).
% 27.04/17.09  tff(c_61937, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_61911, c_61934])).
% 27.04/17.09  tff(c_62040, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_61937])).
% 27.04/17.09  tff(c_61828, plain, (![A_86]: (v1_xboole_0(A_86) | k1_xboole_0!=A_86)), inference(demodulation, [status(thm), theory('equality')], [c_61827, c_61169])).
% 27.04/17.09  tff(c_62052, plain, (![A_86]: (v1_xboole_0(A_86) | A_86!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62040, c_61828])).
% 27.04/17.09  tff(c_61729, plain, (![C_3288, B_3289, A_3290]: (v1_xboole_0(C_3288) | ~m1_subset_1(C_3288, k1_zfmisc_1(k2_zfmisc_1(B_3289, A_3290))) | ~v1_xboole_0(A_3290))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.09  tff(c_61736, plain, (![A_32, A_3290, B_3289]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_3290) | ~r2_hidden(A_32, k2_zfmisc_1(B_3289, A_3290)))), inference(resolution, [status(thm)], [c_40, c_61729])).
% 27.04/17.09  tff(c_62026, plain, (![A_3319, A_3320, B_3321]: (~v1_xboole_0(A_3319) | ~r2_hidden(A_3320, k2_zfmisc_1(B_3321, A_3319)))), inference(negUnitSimplification, [status(thm)], [c_38, c_61736])).
% 27.04/17.09  tff(c_62039, plain, (![A_3319, B_3321]: (~v1_xboole_0(A_3319) | v1_xboole_0(k2_zfmisc_1(B_3321, A_3319)))), inference(resolution, [status(thm)], [c_4, c_62026])).
% 27.04/17.09  tff(c_61914, plain, (![C_3297, A_3298, B_3299]: (v1_xboole_0(C_3297) | ~m1_subset_1(C_3297, k1_zfmisc_1(k2_zfmisc_1(A_3298, B_3299))) | ~v1_xboole_0(A_3298))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.04/17.09  tff(c_61921, plain, (![A_32, A_3298, B_3299]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_3298) | ~r2_hidden(A_32, k2_zfmisc_1(A_3298, B_3299)))), inference(resolution, [status(thm)], [c_40, c_61914])).
% 27.04/17.09  tff(c_62181, plain, (![A_3332, A_3333, B_3334]: (~v1_xboole_0(A_3332) | ~r2_hidden(A_3333, k2_zfmisc_1(A_3332, B_3334)))), inference(negUnitSimplification, [status(thm)], [c_38, c_61921])).
% 27.04/17.09  tff(c_62610, plain, (![A_3351, B_3352]: (~v1_xboole_0(A_3351) | v1_xboole_0(k2_zfmisc_1(A_3351, B_3352)))), inference(resolution, [status(thm)], [c_4, c_62181])).
% 27.04/17.09  tff(c_61148, plain, (![A_3243]: (k1_xboole_0=A_3243 | ~v1_xboole_0(A_3243))), inference(resolution, [status(thm)], [c_61132, c_182])).
% 27.04/17.09  tff(c_62066, plain, (![A_3243]: (A_3243='#skF_8' | ~v1_xboole_0(A_3243))), inference(demodulation, [status(thm), theory('equality')], [c_62040, c_61148])).
% 27.04/17.09  tff(c_62857, plain, (![A_3363, B_3364]: (k2_zfmisc_1(A_3363, B_3364)='#skF_8' | ~v1_xboole_0(A_3363))), inference(resolution, [status(thm)], [c_62610, c_62066])).
% 27.04/17.09  tff(c_62861, plain, (![B_3321, A_3319, B_3364]: (k2_zfmisc_1(k2_zfmisc_1(B_3321, A_3319), B_3364)='#skF_8' | ~v1_xboole_0(A_3319))), inference(resolution, [status(thm)], [c_62039, c_62857])).
% 27.04/17.09  tff(c_64473, plain, (![B_3456, A_3457, B_3458]: (k3_zfmisc_1(B_3456, A_3457, B_3458)='#skF_8' | ~v1_xboole_0(A_3457))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_62861])).
% 27.04/17.09  tff(c_65053, plain, (![B_3456, B_3458]: (k3_zfmisc_1(B_3456, '#skF_8', B_3458)='#skF_8')), inference(resolution, [status(thm)], [c_62052, c_64473])).
% 27.04/17.09  tff(c_61912, plain, (k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_61894, c_82])).
% 27.04/17.09  tff(c_62049, plain, (k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_62040, c_61912])).
% 27.04/17.09  tff(c_65061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65053, c_62049])).
% 27.04/17.09  tff(c_65063, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_61937])).
% 27.04/17.09  tff(c_65078, plain, (![A_3491, B_3492, C_3493, D_3494]: (k5_mcart_1(A_3491, B_3492, C_3493, D_3494)=k1_mcart_1(k1_mcart_1(D_3494)) | ~m1_subset_1(D_3494, k3_zfmisc_1(A_3491, B_3492, C_3493)) | k1_xboole_0=C_3493 | k1_xboole_0=B_3492 | k1_xboole_0=A_3491)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_65081, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60991, c_65078])).
% 27.04/17.09  tff(c_65084, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_61911, c_65063, c_65081])).
% 27.04/17.09  tff(c_65164, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_65084])).
% 27.04/17.09  tff(c_65648, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_65164, c_61828])).
% 27.04/17.09  tff(c_65064, plain, (![A_3489, B_3490]: (~v1_xboole_0(A_3489) | v1_xboole_0(k2_zfmisc_1(B_3490, A_3489)))), inference(resolution, [status(thm)], [c_4, c_62026])).
% 27.04/17.09  tff(c_67352, plain, (![C_3607, A_3608, B_3609]: (~v1_xboole_0(C_3607) | v1_xboole_0(k3_zfmisc_1(A_3608, B_3609, C_3607)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_65064])).
% 27.04/17.09  tff(c_67370, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_67352, c_82])).
% 27.04/17.09  tff(c_67381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65648, c_67370])).
% 27.04/17.09  tff(c_67382, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_65084])).
% 27.04/17.09  tff(c_61241, plain, (![A_3259, B_3260, C_3261]: (k2_zfmisc_1(k2_zfmisc_1(A_3259, B_3260), C_3261)=k3_zfmisc_1(A_3259, B_3260, C_3261))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.09  tff(c_72327, plain, (![A_3837, A_3838, B_3839, C_3840]: (r2_hidden(k1_mcart_1(A_3837), k2_zfmisc_1(A_3838, B_3839)) | ~r2_hidden(A_3837, k3_zfmisc_1(A_3838, B_3839, C_3840)))), inference(superposition, [status(thm), theory('equality')], [c_61241, c_54])).
% 27.04/17.09  tff(c_72368, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_64, c_72327])).
% 27.04/17.09  tff(c_72386, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_7')), inference(resolution, [status(thm)], [c_72368, c_54])).
% 27.04/17.09  tff(c_72404, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_67382, c_72386])).
% 27.04/17.09  tff(c_72406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60992, c_72404])).
% 27.04/17.09  tff(c_72407, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_175])).
% 27.04/17.09  tff(c_72429, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72407, c_60975, c_35324])).
% 27.04/17.09  tff(c_72424, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60975, c_35326])).
% 27.04/17.09  tff(c_73405, plain, (![A_3926, B_3927, C_3928, D_3929]: (k7_mcart_1(A_3926, B_3927, C_3928, D_3929)=k2_mcart_1(D_3929) | ~m1_subset_1(D_3929, k3_zfmisc_1(A_3926, B_3927, C_3928)) | k1_xboole_0=C_3928 | k1_xboole_0=B_3927 | k1_xboole_0=A_3926)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_73409, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_72424, c_73405])).
% 27.04/17.09  tff(c_73510, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_73409])).
% 27.04/17.09  tff(c_72431, plain, (![A_3843, B_3844, C_3845]: (~r1_xboole_0(A_3843, B_3844) | ~r2_hidden(C_3845, k3_xboole_0(A_3843, B_3844)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 27.04/17.09  tff(c_72436, plain, (![A_3843, B_3844]: (~r1_xboole_0(A_3843, B_3844) | v1_xboole_0(k3_xboole_0(A_3843, B_3844)))), inference(resolution, [status(thm)], [c_4, c_72431])).
% 27.04/17.09  tff(c_72521, plain, (![A_3857, B_3858]: (r2_hidden('#skF_2'(A_3857, B_3858), A_3857) | r1_tarski(A_3857, B_3858))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.04/17.09  tff(c_72543, plain, (![A_3859, B_3860]: (~v1_xboole_0(A_3859) | r1_tarski(A_3859, B_3860))), inference(resolution, [status(thm)], [c_72521, c_2])).
% 27.04/17.09  tff(c_72552, plain, (![A_3861]: (k1_xboole_0=A_3861 | ~v1_xboole_0(A_3861))), inference(resolution, [status(thm)], [c_72543, c_182])).
% 27.04/17.09  tff(c_72749, plain, (![A_3889, B_3890]: (k3_xboole_0(A_3889, B_3890)=k1_xboole_0 | ~r1_xboole_0(A_3889, B_3890))), inference(resolution, [status(thm)], [c_72436, c_72552])).
% 27.04/17.09  tff(c_72780, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_72749])).
% 27.04/17.09  tff(c_72452, plain, (![A_3852, B_3853]: (k4_xboole_0(A_3852, k4_xboole_0(A_3852, B_3853))=k3_xboole_0(A_3852, B_3853))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.09  tff(c_72589, plain, (![A_3867, B_3868]: (r1_xboole_0(k3_xboole_0(A_3867, B_3868), k4_xboole_0(A_3867, B_3868)))), inference(superposition, [status(thm), theory('equality')], [c_72452, c_32])).
% 27.04/17.09  tff(c_72651, plain, (![A_3876, B_3877]: (r1_xboole_0(k4_xboole_0(A_3876, B_3877), k3_xboole_0(A_3876, B_3877)))), inference(resolution, [status(thm)], [c_72589, c_12])).
% 27.04/17.09  tff(c_72668, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_72651])).
% 27.04/17.09  tff(c_72825, plain, (![B_3896]: (r1_xboole_0(B_3896, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_72780, c_72668])).
% 27.04/17.09  tff(c_72561, plain, (![A_3843, B_3844]: (k3_xboole_0(A_3843, B_3844)=k1_xboole_0 | ~r1_xboole_0(A_3843, B_3844))), inference(resolution, [status(thm)], [c_72436, c_72552])).
% 27.04/17.09  tff(c_72844, plain, (![B_3896]: (k3_xboole_0(B_3896, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72825, c_72561])).
% 27.04/17.09  tff(c_72934, plain, (![B_3903]: (k4_xboole_0(B_3903, k1_xboole_0)=B_3903)), inference(resolution, [status(thm)], [c_72825, c_34])).
% 27.04/17.09  tff(c_72955, plain, (![B_3903]: (k4_xboole_0(B_3903, B_3903)=k3_xboole_0(B_3903, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_72934, c_26])).
% 27.04/17.09  tff(c_73305, plain, (![B_3903]: (k4_xboole_0(B_3903, B_3903)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72844, c_72955])).
% 27.04/17.09  tff(c_72487, plain, (![B_3854]: (k3_xboole_0(B_3854, B_3854)=B_3854)), inference(superposition, [status(thm), theory('equality')], [c_72452, c_104])).
% 27.04/17.09  tff(c_72503, plain, (![B_3855]: (~r1_xboole_0(B_3855, B_3855) | v1_xboole_0(B_3855))), inference(superposition, [status(thm), theory('equality')], [c_72487, c_72436])).
% 27.04/17.09  tff(c_72513, plain, (![B_30]: (v1_xboole_0(B_30) | k4_xboole_0(B_30, B_30)!=B_30)), inference(resolution, [status(thm)], [c_36, c_72503])).
% 27.04/17.09  tff(c_73306, plain, (![B_30]: (v1_xboole_0(B_30) | k1_xboole_0!=B_30)), inference(demodulation, [status(thm), theory('equality')], [c_73305, c_72513])).
% 27.04/17.09  tff(c_73521, plain, (![B_30]: (v1_xboole_0(B_30) | B_30!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73510, c_73306])).
% 27.04/17.09  tff(c_73151, plain, (![C_3910, A_3911, B_3912]: (v1_xboole_0(C_3910) | ~m1_subset_1(C_3910, k1_zfmisc_1(k2_zfmisc_1(A_3911, B_3912))) | ~v1_xboole_0(A_3911))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.04/17.09  tff(c_73158, plain, (![A_32, A_3911, B_3912]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_3911) | ~r2_hidden(A_32, k2_zfmisc_1(A_3911, B_3912)))), inference(resolution, [status(thm)], [c_40, c_73151])).
% 27.04/17.09  tff(c_73496, plain, (![A_3944, A_3945, B_3946]: (~v1_xboole_0(A_3944) | ~r2_hidden(A_3945, k2_zfmisc_1(A_3944, B_3946)))), inference(negUnitSimplification, [status(thm)], [c_38, c_73158])).
% 27.04/17.09  tff(c_73509, plain, (![A_3944, B_3946]: (~v1_xboole_0(A_3944) | v1_xboole_0(k2_zfmisc_1(A_3944, B_3946)))), inference(resolution, [status(thm)], [c_4, c_73496])).
% 27.04/17.09  tff(c_74115, plain, (![A_3975, B_3976]: (~v1_xboole_0(A_3975) | v1_xboole_0(k2_zfmisc_1(A_3975, B_3976)))), inference(resolution, [status(thm)], [c_4, c_73496])).
% 27.04/17.09  tff(c_72550, plain, (![A_3859]: (k1_xboole_0=A_3859 | ~v1_xboole_0(A_3859))), inference(resolution, [status(thm)], [c_72543, c_182])).
% 27.04/17.09  tff(c_73535, plain, (![A_3859]: (A_3859='#skF_4' | ~v1_xboole_0(A_3859))), inference(demodulation, [status(thm), theory('equality')], [c_73510, c_72550])).
% 27.04/17.09  tff(c_74402, plain, (![A_3992, B_3993]: (k2_zfmisc_1(A_3992, B_3993)='#skF_4' | ~v1_xboole_0(A_3992))), inference(resolution, [status(thm)], [c_74115, c_73535])).
% 27.04/17.09  tff(c_74404, plain, (![A_3944, B_3946, B_3993]: (k2_zfmisc_1(k2_zfmisc_1(A_3944, B_3946), B_3993)='#skF_4' | ~v1_xboole_0(A_3944))), inference(resolution, [status(thm)], [c_73509, c_74402])).
% 27.04/17.09  tff(c_75956, plain, (![A_4086, B_4087, B_4088]: (k3_zfmisc_1(A_4086, B_4087, B_4088)='#skF_4' | ~v1_xboole_0(A_4086))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_74404])).
% 27.04/17.09  tff(c_76279, plain, (![B_4087, B_4088]: (k3_zfmisc_1('#skF_4', B_4087, B_4088)='#skF_4')), inference(resolution, [status(thm)], [c_73521, c_75956])).
% 27.04/17.09  tff(c_73932, plain, (![B_3967]: (v1_xboole_0(B_3967) | B_3967!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73510, c_73306])).
% 27.04/17.09  tff(c_72410, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_72407, c_82])).
% 27.04/17.09  tff(c_73950, plain, (k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9')!='#skF_4'), inference(resolution, [status(thm)], [c_73932, c_72410])).
% 27.04/17.09  tff(c_76287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76279, c_73950])).
% 27.04/17.09  tff(c_76289, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_73409])).
% 27.04/17.09  tff(c_73482, plain, (![A_3938, B_3939, C_3940, D_3941]: (k5_mcart_1(A_3938, B_3939, C_3940, D_3941)=k1_mcart_1(k1_mcart_1(D_3941)) | ~m1_subset_1(D_3941, k3_zfmisc_1(A_3938, B_3939, C_3940)) | k1_xboole_0=C_3940 | k1_xboole_0=B_3939 | k1_xboole_0=A_3938)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_73486, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_72424, c_73482])).
% 27.04/17.09  tff(c_76290, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_73486])).
% 27.04/17.09  tff(c_76291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76289, c_76290])).
% 27.04/17.09  tff(c_76292, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9' | k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_73486])).
% 27.04/17.09  tff(c_76652, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_76292])).
% 27.04/17.09  tff(c_72411, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_72407, c_64])).
% 27.04/17.09  tff(c_72699, plain, (![A_3880, B_3881, C_3882]: (r2_hidden(k1_mcart_1(A_3880), B_3881) | ~r2_hidden(A_3880, k2_zfmisc_1(B_3881, C_3882)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_84820, plain, (![A_4517, A_4518, B_4519, C_4520]: (r2_hidden(k1_mcart_1(A_4517), k2_zfmisc_1(A_4518, B_4519)) | ~r2_hidden(A_4517, k3_zfmisc_1(A_4518, B_4519, C_4520)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_72699])).
% 27.04/17.09  tff(c_84863, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_72411, c_84820])).
% 27.04/17.09  tff(c_84882, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_4')), inference(resolution, [status(thm)], [c_84863, c_54])).
% 27.04/17.09  tff(c_84900, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76652, c_84882])).
% 27.04/17.09  tff(c_84902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72429, c_84900])).
% 27.04/17.09  tff(c_84903, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_76292])).
% 27.04/17.09  tff(c_84905, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_84903])).
% 27.04/17.09  tff(c_85481, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84905, c_73306])).
% 27.04/17.09  tff(c_87357, plain, (![B_4641, C_4642]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_4641, C_4642))), B_4641) | v1_xboole_0(k2_zfmisc_1(B_4641, C_4642)))), inference(resolution, [status(thm)], [c_4, c_72699])).
% 27.04/17.09  tff(c_73370, plain, (![C_3921, B_3922, A_3923]: (v1_xboole_0(C_3921) | ~m1_subset_1(C_3921, k1_zfmisc_1(k2_zfmisc_1(B_3922, A_3923))) | ~v1_xboole_0(A_3923))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.09  tff(c_73377, plain, (![A_32, A_3923, B_3922]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_3923) | ~r2_hidden(A_32, k2_zfmisc_1(B_3922, A_3923)))), inference(resolution, [status(thm)], [c_40, c_73370])).
% 27.04/17.09  tff(c_73384, plain, (![A_3923, A_32, B_3922]: (~v1_xboole_0(A_3923) | ~r2_hidden(A_32, k2_zfmisc_1(B_3922, A_3923)))), inference(negUnitSimplification, [status(thm)], [c_38, c_73377])).
% 27.04/17.09  tff(c_87374, plain, (![A_3923, B_3922, C_4642]: (~v1_xboole_0(A_3923) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_3922, A_3923), C_4642)))), inference(resolution, [status(thm)], [c_87357, c_73384])).
% 27.04/17.09  tff(c_87462, plain, (![A_4645, B_4646, C_4647]: (~v1_xboole_0(A_4645) | v1_xboole_0(k3_zfmisc_1(B_4646, A_4645, C_4647)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_87374])).
% 27.04/17.09  tff(c_87484, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_87462, c_72410])).
% 27.04/17.09  tff(c_87497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85481, c_87484])).
% 27.04/17.09  tff(c_87498, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_84903])).
% 27.04/17.09  tff(c_72794, plain, (![B_3894, A_3895]: (k3_xboole_0(B_3894, k4_xboole_0(A_3895, B_3894))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_72749])).
% 27.04/17.09  tff(c_72808, plain, (![B_3894, A_3895, C_16]: (~r1_xboole_0(B_3894, k4_xboole_0(A_3895, B_3894)) | ~r2_hidden(C_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_72794, c_16])).
% 27.04/17.09  tff(c_72823, plain, (![C_16]: (~r2_hidden(C_16, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_72808])).
% 27.04/17.09  tff(c_87526, plain, (![C_16]: (~r2_hidden(C_16, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_87498, c_72823])).
% 27.04/17.09  tff(c_73019, plain, (![A_3905, C_3906, B_3907]: (r2_hidden(k2_mcart_1(A_3905), C_3906) | ~r2_hidden(A_3905, k2_zfmisc_1(B_3907, C_3906)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_89005, plain, (![A_4722, C_4723, A_4724, B_4725]: (r2_hidden(k2_mcart_1(A_4722), C_4723) | ~r2_hidden(A_4722, k3_zfmisc_1(A_4724, B_4725, C_4723)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_73019])).
% 27.04/17.09  tff(c_89013, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_72411, c_89005])).
% 27.04/17.09  tff(c_89022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87526, c_89013])).
% 27.04/17.09  tff(c_89023, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8') | ~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_62])).
% 27.04/17.09  tff(c_89104, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_89023])).
% 27.04/17.09  tff(c_90335, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_90314, c_89104])).
% 27.04/17.09  tff(c_89295, plain, (![A_4766, C_4767, B_4768]: (r2_hidden(k2_mcart_1(A_4766), C_4767) | ~r2_hidden(A_4766, k2_zfmisc_1(B_4768, C_4767)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_93543, plain, (![A_5026, C_5027, A_5028, B_5029]: (r2_hidden(k2_mcart_1(A_5026), C_5027) | ~r2_hidden(A_5026, k3_zfmisc_1(A_5028, B_5029, C_5027)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_89295])).
% 27.04/17.09  tff(c_93566, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_64, c_93543])).
% 27.04/17.09  tff(c_93575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90335, c_93566])).
% 27.04/17.09  tff(c_93576, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_89123])).
% 27.04/17.09  tff(c_93581, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_93576, c_66])).
% 27.04/17.09  tff(c_95313, plain, (![A_5163, B_5164, C_5165, D_5166]: (k7_mcart_1(A_5163, B_5164, C_5165, D_5166)=k2_mcart_1(D_5166) | ~m1_subset_1(D_5166, k3_zfmisc_1(A_5163, B_5164, C_5165)) | k1_xboole_0=C_5165 | k1_xboole_0=B_5164 | k1_xboole_0=A_5163)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_95316, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_93581, c_95313])).
% 27.04/17.09  tff(c_95319, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_94332, c_94333, c_95316])).
% 27.04/17.09  tff(c_95380, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_95319])).
% 27.04/17.09  tff(c_94247, plain, (![B_30]: (v1_xboole_0(B_30) | k1_xboole_0!=B_30)), inference(demodulation, [status(thm), theory('equality')], [c_94225, c_93604])).
% 27.04/17.09  tff(c_95760, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_95380, c_94247])).
% 27.04/17.09  tff(c_94433, plain, (![A_5085, B_5086, C_5087]: (r2_hidden(k1_mcart_1(A_5085), B_5086) | ~r2_hidden(A_5085, k2_zfmisc_1(B_5086, C_5087)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_98333, plain, (![B_5305, C_5306]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_5305, C_5306))), B_5305) | v1_xboole_0(k2_zfmisc_1(B_5305, C_5306)))), inference(resolution, [status(thm)], [c_4, c_94433])).
% 27.04/17.09  tff(c_94579, plain, (![C_5101, B_5102, A_5103]: (v1_xboole_0(C_5101) | ~m1_subset_1(C_5101, k1_zfmisc_1(k2_zfmisc_1(B_5102, A_5103))) | ~v1_xboole_0(A_5103))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.09  tff(c_94586, plain, (![A_32, A_5103, B_5102]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_5103) | ~r2_hidden(A_32, k2_zfmisc_1(B_5102, A_5103)))), inference(resolution, [status(thm)], [c_40, c_94579])).
% 27.04/17.09  tff(c_94593, plain, (![A_5103, A_32, B_5102]: (~v1_xboole_0(A_5103) | ~r2_hidden(A_32, k2_zfmisc_1(B_5102, A_5103)))), inference(negUnitSimplification, [status(thm)], [c_38, c_94586])).
% 27.04/17.09  tff(c_98354, plain, (![A_5103, B_5102, C_5306]: (~v1_xboole_0(A_5103) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_5102, A_5103), C_5306)))), inference(resolution, [status(thm)], [c_98333, c_94593])).
% 27.04/17.09  tff(c_98465, plain, (![A_5312, B_5313, C_5314]: (~v1_xboole_0(A_5312) | v1_xboole_0(k3_zfmisc_1(B_5313, A_5312, C_5314)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_98354])).
% 27.04/17.09  tff(c_98485, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_98465, c_82])).
% 27.04/17.09  tff(c_98497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95760, c_98485])).
% 27.04/17.09  tff(c_98498, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_95319])).
% 27.04/17.09  tff(c_93578, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_93576, c_89104])).
% 27.04/17.09  tff(c_98784, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_98498, c_93578])).
% 27.04/17.09  tff(c_94338, plain, (![A_5078, B_5079, C_5080]: (k2_zfmisc_1(k2_zfmisc_1(A_5078, B_5079), C_5080)=k3_zfmisc_1(A_5078, B_5079, C_5080))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.09  tff(c_52, plain, (![A_47, C_49, B_48]: (r2_hidden(k2_mcart_1(A_47), C_49) | ~r2_hidden(A_47, k2_zfmisc_1(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_102231, plain, (![A_5486, C_5487, A_5488, B_5489]: (r2_hidden(k2_mcart_1(A_5486), C_5487) | ~r2_hidden(A_5486, k3_zfmisc_1(A_5488, B_5489, C_5487)))), inference(superposition, [status(thm), theory('equality')], [c_94338, c_52])).
% 27.04/17.09  tff(c_102254, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_64, c_102231])).
% 27.04/17.09  tff(c_102263, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98784, c_102254])).
% 27.04/17.09  tff(c_102264, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_89122])).
% 27.04/17.09  tff(c_89024, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 27.04/17.09  tff(c_89064, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_89024, c_2])).
% 27.04/17.09  tff(c_102266, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102264, c_89064])).
% 27.04/17.09  tff(c_108438, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_108418, c_102266])).
% 27.04/17.09  tff(c_108439, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_108418, c_89197])).
% 27.04/17.09  tff(c_102516, plain, (![A_5518, B_5519]: (k3_xboole_0(A_5518, B_5519)=k1_xboole_0 | ~r1_xboole_0(A_5518, B_5519))), inference(resolution, [status(thm)], [c_89102, c_89153])).
% 27.04/17.09  tff(c_102543, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_102516])).
% 27.04/17.09  tff(c_102366, plain, (![A_5500, B_5501]: (r1_xboole_0(k3_xboole_0(A_5500, B_5501), k4_xboole_0(A_5500, B_5501)))), inference(superposition, [status(thm), theory('equality')], [c_89159, c_32])).
% 27.04/17.09  tff(c_102383, plain, (![B_28, A_27]: (r1_xboole_0(k3_xboole_0(B_28, k4_xboole_0(A_27, B_28)), B_28))), inference(superposition, [status(thm), theory('equality')], [c_104, c_102366])).
% 27.04/17.09  tff(c_102577, plain, (![B_5522]: (r1_xboole_0(k1_xboole_0, B_5522))), inference(demodulation, [status(thm), theory('equality')], [c_102543, c_102383])).
% 27.04/17.09  tff(c_102628, plain, (![B_5524]: (r1_xboole_0(B_5524, k1_xboole_0))), inference(resolution, [status(thm)], [c_102577, c_12])).
% 27.04/17.09  tff(c_102647, plain, (![B_5524]: (k3_xboole_0(B_5524, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_102628, c_89157])).
% 27.04/17.09  tff(c_102748, plain, (![B_5531]: (k4_xboole_0(k1_xboole_0, B_5531)=k1_xboole_0)), inference(resolution, [status(thm)], [c_102577, c_34])).
% 27.04/17.09  tff(c_102855, plain, (![B_5533]: (k4_xboole_0(B_5533, k1_xboole_0)=B_5533)), inference(superposition, [status(thm), theory('equality')], [c_102748, c_104])).
% 27.04/17.09  tff(c_102880, plain, (![B_5533]: (k4_xboole_0(B_5533, B_5533)=k3_xboole_0(B_5533, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_102855, c_26])).
% 27.04/17.09  tff(c_102906, plain, (![B_5533]: (k4_xboole_0(B_5533, B_5533)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_102647, c_102880])).
% 27.04/17.09  tff(c_102306, plain, (![A_5492]: (~r1_xboole_0(A_5492, A_5492) | v1_xboole_0(A_5492))), inference(superposition, [status(thm), theory('equality')], [c_89198, c_89102])).
% 27.04/17.09  tff(c_102315, plain, (![A_4730]: (v1_xboole_0(A_4730) | k4_xboole_0(A_4730, A_4730)!=A_4730)), inference(resolution, [status(thm)], [c_89060, c_102306])).
% 27.04/17.09  tff(c_103002, plain, (![A_5538]: (v1_xboole_0(A_5538) | k1_xboole_0!=A_5538)), inference(demodulation, [status(thm), theory('equality')], [c_102906, c_102315])).
% 27.04/17.09  tff(c_103026, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_103002, c_102266])).
% 27.04/17.09  tff(c_102284, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_89123])).
% 27.04/17.09  tff(c_102288, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_89090, c_102284])).
% 27.04/17.09  tff(c_103025, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_103002, c_102288])).
% 27.04/17.09  tff(c_103027, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_103002, c_89197])).
% 27.04/17.09  tff(c_103778, plain, (![A_5605, B_5606, C_5607, D_5608]: (k7_mcart_1(A_5605, B_5606, C_5607, D_5608)=k2_mcart_1(D_5608) | ~m1_subset_1(D_5608, k3_zfmisc_1(A_5605, B_5606, C_5607)) | k1_xboole_0=C_5607 | k1_xboole_0=B_5606 | k1_xboole_0=A_5605)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_103781, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_103778])).
% 27.04/17.09  tff(c_103784, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_103026, c_103025, c_103027, c_103781])).
% 27.04/17.09  tff(c_103785, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_103784, c_89104])).
% 27.04/17.09  tff(c_102270, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_102264, c_64])).
% 27.04/17.09  tff(c_102675, plain, (![A_5526, C_5527, B_5528]: (r2_hidden(k2_mcart_1(A_5526), C_5527) | ~r2_hidden(A_5526, k2_zfmisc_1(B_5528, C_5527)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_107620, plain, (![A_5796, C_5797, A_5798, B_5799]: (r2_hidden(k2_mcart_1(A_5796), C_5797) | ~r2_hidden(A_5796, k3_zfmisc_1(A_5798, B_5799, C_5797)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_102675])).
% 27.04/17.09  tff(c_107637, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_102270, c_107620])).
% 27.04/17.09  tff(c_107650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103785, c_107637])).
% 27.04/17.09  tff(c_107651, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_89123])).
% 27.04/17.09  tff(c_107655, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_107651, c_66])).
% 27.04/17.09  tff(c_109176, plain, (![A_5918, B_5919, C_5920, D_5921]: (k7_mcart_1(A_5918, B_5919, C_5920, D_5921)=k2_mcart_1(D_5921) | ~m1_subset_1(D_5921, k3_zfmisc_1(A_5918, B_5919, C_5920)) | k1_xboole_0=C_5920 | k1_xboole_0=B_5919 | k1_xboole_0=A_5918)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_109179, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_107655, c_109176])).
% 27.04/17.09  tff(c_109182, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_108438, c_108439, c_109179])).
% 27.04/17.09  tff(c_109215, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_109182])).
% 27.04/17.09  tff(c_108332, plain, (![B_30]: (v1_xboole_0(B_30) | k1_xboole_0!=B_30)), inference(demodulation, [status(thm), theory('equality')], [c_108258, c_107678])).
% 27.04/17.09  tff(c_109739, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_109215, c_108332])).
% 27.04/17.09  tff(c_108318, plain, (![A_5846, B_5847, C_5848]: (r2_hidden(k1_mcart_1(A_5846), B_5847) | ~r2_hidden(A_5846, k2_zfmisc_1(B_5847, C_5848)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_112351, plain, (![B_6089, C_6090]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_6089, C_6090))), B_6089) | v1_xboole_0(k2_zfmisc_1(B_6089, C_6090)))), inference(resolution, [status(thm)], [c_4, c_108318])).
% 27.04/17.09  tff(c_108756, plain, (![C_5876, B_5877, A_5878]: (v1_xboole_0(C_5876) | ~m1_subset_1(C_5876, k1_zfmisc_1(k2_zfmisc_1(B_5877, A_5878))) | ~v1_xboole_0(A_5878))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.09  tff(c_108763, plain, (![A_32, A_5878, B_5877]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_5878) | ~r2_hidden(A_32, k2_zfmisc_1(B_5877, A_5878)))), inference(resolution, [status(thm)], [c_40, c_108756])).
% 27.04/17.09  tff(c_108770, plain, (![A_5878, A_32, B_5877]: (~v1_xboole_0(A_5878) | ~r2_hidden(A_32, k2_zfmisc_1(B_5877, A_5878)))), inference(negUnitSimplification, [status(thm)], [c_38, c_108763])).
% 27.04/17.09  tff(c_112372, plain, (![A_5878, B_5877, C_6090]: (~v1_xboole_0(A_5878) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_5877, A_5878), C_6090)))), inference(resolution, [status(thm)], [c_112351, c_108770])).
% 27.04/17.09  tff(c_112507, plain, (![A_6096, B_6097, C_6098]: (~v1_xboole_0(A_6096) | v1_xboole_0(k3_zfmisc_1(B_6097, A_6096, C_6098)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_112372])).
% 27.04/17.09  tff(c_102269, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_102264, c_82])).
% 27.04/17.09  tff(c_112535, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_112507, c_102269])).
% 27.04/17.09  tff(c_112551, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109739, c_112535])).
% 27.04/17.09  tff(c_112552, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_109182])).
% 27.04/17.09  tff(c_107653, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_107651, c_89104])).
% 27.04/17.09  tff(c_112554, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_112552, c_107653])).
% 27.04/17.09  tff(c_108467, plain, (![A_5855, B_5856, C_5857]: (k2_zfmisc_1(k2_zfmisc_1(A_5855, B_5856), C_5857)=k3_zfmisc_1(A_5855, B_5856, C_5857))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.09  tff(c_117026, plain, (![A_6308, C_6309, A_6310, B_6311]: (r2_hidden(k2_mcart_1(A_6308), C_6309) | ~r2_hidden(A_6308, k3_zfmisc_1(A_6310, B_6311, C_6309)))), inference(superposition, [status(thm), theory('equality')], [c_108467, c_52])).
% 27.04/17.09  tff(c_117043, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_102270, c_117026])).
% 27.04/17.09  tff(c_117056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112554, c_117043])).
% 27.04/17.09  tff(c_117057, plain, ('#skF_6'='#skF_9'), inference(splitRight, [status(thm)], [c_89124])).
% 27.04/17.09  tff(c_117062, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_117057, c_66])).
% 27.04/17.09  tff(c_118279, plain, (![A_6400, B_6401, C_6402, D_6403]: (k7_mcart_1(A_6400, B_6401, C_6402, D_6403)=k2_mcart_1(D_6403) | ~m1_subset_1(D_6403, k3_zfmisc_1(A_6400, B_6401, C_6402)) | k1_xboole_0=C_6402 | k1_xboole_0=B_6401 | k1_xboole_0=A_6400)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_118282, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_117062, c_118279])).
% 27.04/17.09  tff(c_118285, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_118051, c_118050, c_118282])).
% 27.04/17.09  tff(c_118347, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_118285])).
% 27.04/17.09  tff(c_117407, plain, (![B_6346, A_6347]: (k3_xboole_0(B_6346, k4_xboole_0(A_6347, B_6346))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_117372])).
% 27.04/17.09  tff(c_117421, plain, (![B_6346, A_6347, C_16]: (~r1_xboole_0(B_6346, k4_xboole_0(A_6347, B_6346)) | ~r2_hidden(C_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_117407, c_16])).
% 27.04/17.09  tff(c_117436, plain, (![C_16]: (~r2_hidden(C_16, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_117421])).
% 27.04/17.09  tff(c_118373, plain, (![C_16]: (~r2_hidden(C_16, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_118347, c_117436])).
% 27.04/17.09  tff(c_117688, plain, (![A_6360, B_6361, C_6362]: (k2_zfmisc_1(k2_zfmisc_1(A_6360, B_6361), C_6362)=k3_zfmisc_1(A_6360, B_6361, C_6362))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.09  tff(c_120545, plain, (![A_6523, C_6524, A_6525, B_6526]: (r2_hidden(k2_mcart_1(A_6523), C_6524) | ~r2_hidden(A_6523, k3_zfmisc_1(A_6525, B_6526, C_6524)))), inference(superposition, [status(thm), theory('equality')], [c_117688, c_52])).
% 27.04/17.09  tff(c_120559, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_64, c_120545])).
% 27.04/17.09  tff(c_120567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118373, c_120559])).
% 27.04/17.09  tff(c_120568, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_118285])).
% 27.04/17.09  tff(c_117059, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_117057, c_89104])).
% 27.04/17.09  tff(c_120613, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_120568, c_117059])).
% 27.04/17.09  tff(c_123487, plain, (![A_6699, C_6700, A_6701, B_6702]: (r2_hidden(k2_mcart_1(A_6699), C_6700) | ~r2_hidden(A_6699, k3_zfmisc_1(A_6701, B_6702, C_6700)))), inference(superposition, [status(thm), theory('equality')], [c_117688, c_52])).
% 27.04/17.09  tff(c_123510, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_64, c_123487])).
% 27.04/17.09  tff(c_123519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120613, c_123510])).
% 27.04/17.09  tff(c_123520, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_89123])).
% 27.04/17.09  tff(c_123522, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_123520, c_117062])).
% 27.04/17.09  tff(c_125163, plain, (![A_6831, B_6832, C_6833, D_6834]: (k7_mcart_1(A_6831, B_6832, C_6833, D_6834)=k2_mcart_1(D_6834) | ~m1_subset_1(D_6834, k3_zfmisc_1(A_6831, B_6832, C_6833)) | k1_xboole_0=C_6833 | k1_xboole_0=B_6832 | k1_xboole_0=A_6831)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_125166, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_123522, c_125163])).
% 27.04/17.09  tff(c_125169, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_124238, c_124713, c_125166])).
% 27.04/17.09  tff(c_125201, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_125169])).
% 27.04/17.09  tff(c_124504, plain, (![A_6775, B_6777]: (~v1_xboole_0(A_6775) | v1_xboole_0(k2_zfmisc_1(B_6777, A_6775)))), inference(resolution, [status(thm)], [c_4, c_124491])).
% 27.04/17.09  tff(c_124691, plain, (![C_6793, A_6794, B_6795]: (v1_xboole_0(C_6793) | ~m1_subset_1(C_6793, k1_zfmisc_1(k2_zfmisc_1(A_6794, B_6795))) | ~v1_xboole_0(A_6794))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.04/17.09  tff(c_124701, plain, (![A_32, A_6794, B_6795]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_6794) | ~r2_hidden(A_32, k2_zfmisc_1(A_6794, B_6795)))), inference(resolution, [status(thm)], [c_40, c_124691])).
% 27.04/17.09  tff(c_124714, plain, (![A_6796, A_6797, B_6798]: (~v1_xboole_0(A_6796) | ~r2_hidden(A_6797, k2_zfmisc_1(A_6796, B_6798)))), inference(negUnitSimplification, [status(thm)], [c_38, c_124701])).
% 27.04/17.09  tff(c_124747, plain, (![A_6801, B_6802]: (~v1_xboole_0(A_6801) | v1_xboole_0(k2_zfmisc_1(A_6801, B_6802)))), inference(resolution, [status(thm)], [c_4, c_124714])).
% 27.04/17.09  tff(c_89147, plain, (![A_4740]: (k1_xboole_0=A_4740 | ~v1_xboole_0(A_4740))), inference(resolution, [status(thm)], [c_89090, c_89130])).
% 27.04/17.09  tff(c_124768, plain, (![A_6803, B_6804]: (k2_zfmisc_1(A_6803, B_6804)=k1_xboole_0 | ~v1_xboole_0(A_6803))), inference(resolution, [status(thm)], [c_124747, c_89147])).
% 27.04/17.09  tff(c_124774, plain, (![B_6777, A_6775, B_6804]: (k2_zfmisc_1(k2_zfmisc_1(B_6777, A_6775), B_6804)=k1_xboole_0 | ~v1_xboole_0(A_6775))), inference(resolution, [status(thm)], [c_124504, c_124768])).
% 27.04/17.09  tff(c_125036, plain, (![B_6823, A_6824, B_6825]: (k3_zfmisc_1(B_6823, A_6824, B_6825)=k1_xboole_0 | ~v1_xboole_0(A_6824))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_124774])).
% 27.04/17.09  tff(c_125050, plain, (![B_6823, B_30, B_6825]: (k3_zfmisc_1(B_6823, B_30, B_6825)=k1_xboole_0 | k1_xboole_0!=B_30)), inference(resolution, [status(thm)], [c_124144, c_125036])).
% 27.04/17.09  tff(c_128750, plain, (![B_6823, B_6825]: (k3_zfmisc_1(B_6823, '#skF_8', B_6825)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_125201, c_125201, c_125050])).
% 27.04/17.09  tff(c_124241, plain, (k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_124219, c_82])).
% 27.04/17.09  tff(c_125226, plain, (k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_125201, c_124241])).
% 27.04/17.09  tff(c_128758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128750, c_125226])).
% 27.04/17.09  tff(c_128759, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_125169])).
% 27.04/17.09  tff(c_123749, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_123520, c_117059])).
% 27.04/17.09  tff(c_128768, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_128759, c_123749])).
% 27.04/17.09  tff(c_123914, plain, (![A_6737, C_6738, B_6739]: (r2_hidden(k2_mcart_1(A_6737), C_6738) | ~r2_hidden(A_6737, k2_zfmisc_1(B_6739, C_6738)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_132820, plain, (![A_7204, C_7205, A_7206, B_7207]: (r2_hidden(k2_mcart_1(A_7204), C_7205) | ~r2_hidden(A_7204, k3_zfmisc_1(A_7206, B_7207, C_7205)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_123914])).
% 27.04/17.09  tff(c_132846, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_64, c_132820])).
% 27.04/17.09  tff(c_132856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128768, c_132846])).
% 27.04/17.09  tff(c_132857, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_89122])).
% 27.04/17.09  tff(c_132861, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_132857, c_82])).
% 27.04/17.09  tff(c_144961, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_144939, c_132861])).
% 27.04/17.09  tff(c_144973, plain, (k1_xboole_0!='#skF_9'), inference(resolution, [status(thm)], [c_140748, c_144961])).
% 27.04/17.09  tff(c_140814, plain, (![A_7676]: (v1_xboole_0(A_7676) | k1_xboole_0!=A_7676)), inference(demodulation, [status(thm), theory('equality')], [c_140747, c_140016])).
% 27.04/17.09  tff(c_132859, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_132857, c_89064])).
% 27.04/17.09  tff(c_140831, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_140814, c_132859])).
% 27.04/17.09  tff(c_133149, plain, (![A_7237, B_7238]: (k3_xboole_0(A_7237, B_7238)=k1_xboole_0 | ~r1_xboole_0(A_7237, B_7238))), inference(resolution, [status(thm)], [c_89102, c_89153])).
% 27.04/17.09  tff(c_133180, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_133149])).
% 27.04/17.09  tff(c_132892, plain, (![A_7209, B_7210]: (k4_xboole_0(A_7209, k4_xboole_0(A_7209, B_7210))=k3_xboole_0(A_7209, B_7210))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.09  tff(c_132991, plain, (![A_7218, B_7219]: (r1_xboole_0(k3_xboole_0(A_7218, B_7219), k4_xboole_0(A_7218, B_7219)))), inference(superposition, [status(thm), theory('equality')], [c_132892, c_32])).
% 27.04/17.09  tff(c_133044, plain, (![A_7224, B_7225]: (r1_xboole_0(k4_xboole_0(A_7224, B_7225), k3_xboole_0(A_7224, B_7225)))), inference(resolution, [status(thm)], [c_132991, c_12])).
% 27.04/17.09  tff(c_133061, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_133044])).
% 27.04/17.09  tff(c_133283, plain, (![B_7247]: (r1_xboole_0(B_7247, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_133180, c_133061])).
% 27.04/17.09  tff(c_133306, plain, (![B_7247]: (k3_xboole_0(B_7247, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_133283, c_89157])).
% 27.04/17.09  tff(c_133480, plain, (![B_7257]: (k4_xboole_0(B_7257, k1_xboole_0)=B_7257)), inference(resolution, [status(thm)], [c_133283, c_34])).
% 27.04/17.09  tff(c_133508, plain, (![B_7257]: (k4_xboole_0(B_7257, B_7257)=k3_xboole_0(B_7257, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_133480, c_26])).
% 27.04/17.09  tff(c_133534, plain, (![B_7257]: (k4_xboole_0(B_7257, B_7257)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_133306, c_133508])).
% 27.04/17.09  tff(c_132927, plain, (![B_7211]: (k3_xboole_0(B_7211, B_7211)=B_7211)), inference(superposition, [status(thm), theory('equality')], [c_132892, c_104])).
% 27.04/17.09  tff(c_132943, plain, (![B_7212]: (~r1_xboole_0(B_7212, B_7212) | v1_xboole_0(B_7212))), inference(superposition, [status(thm), theory('equality')], [c_132927, c_89102])).
% 27.04/17.09  tff(c_132953, plain, (![B_30]: (v1_xboole_0(B_30) | k4_xboole_0(B_30, B_30)!=B_30)), inference(resolution, [status(thm)], [c_36, c_132943])).
% 27.04/17.09  tff(c_133684, plain, (![B_7264]: (v1_xboole_0(B_7264) | k1_xboole_0!=B_7264)), inference(demodulation, [status(thm), theory('equality')], [c_133534, c_132953])).
% 27.04/17.09  tff(c_133705, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_133684, c_132859])).
% 27.04/17.09  tff(c_132875, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_89123])).
% 27.04/17.09  tff(c_132879, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_89090, c_132875])).
% 27.04/17.09  tff(c_133704, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_133684, c_132879])).
% 27.04/17.09  tff(c_134172, plain, (![A_7307, B_7308, C_7309, D_7310]: (k7_mcart_1(A_7307, B_7308, C_7309, D_7310)=k2_mcart_1(D_7310) | ~m1_subset_1(D_7310, k3_zfmisc_1(A_7307, B_7308, C_7309)) | k1_xboole_0=C_7309 | k1_xboole_0=B_7308 | k1_xboole_0=A_7307)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_134175, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_117062, c_134172])).
% 27.04/17.09  tff(c_134178, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_133705, c_133704, c_134175])).
% 27.04/17.09  tff(c_134287, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_134178])).
% 27.04/17.09  tff(c_133207, plain, (![A_7242, B_7243]: (k3_xboole_0(k4_xboole_0(A_7242, B_7243), B_7243)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_133149])).
% 27.04/17.09  tff(c_133221, plain, (![A_7242, B_7243, C_16]: (~r1_xboole_0(k4_xboole_0(A_7242, B_7243), B_7243) | ~r2_hidden(C_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_133207, c_16])).
% 27.04/17.09  tff(c_133234, plain, (![C_16]: (~r2_hidden(C_16, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_133221])).
% 27.04/17.09  tff(c_134316, plain, (![C_16]: (~r2_hidden(C_16, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_134287, c_133234])).
% 27.04/17.09  tff(c_132862, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_132857, c_64])).
% 27.04/17.09  tff(c_133345, plain, (![A_7249, C_7250, B_7251]: (r2_hidden(k2_mcart_1(A_7249), C_7250) | ~r2_hidden(A_7249, k2_zfmisc_1(B_7251, C_7250)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_136539, plain, (![A_7428, C_7429, A_7430, B_7431]: (r2_hidden(k2_mcart_1(A_7428), C_7429) | ~r2_hidden(A_7428, k3_zfmisc_1(A_7430, B_7431, C_7429)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_133345])).
% 27.04/17.09  tff(c_136547, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_132862, c_136539])).
% 27.04/17.09  tff(c_136559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134316, c_136547])).
% 27.04/17.09  tff(c_136560, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_134178])).
% 27.04/17.09  tff(c_136629, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_136560, c_117059])).
% 27.04/17.09  tff(c_139886, plain, (![A_7615, C_7616, A_7617, B_7618]: (r2_hidden(k2_mcart_1(A_7615), C_7616) | ~r2_hidden(A_7615, k3_zfmisc_1(A_7617, B_7618, C_7616)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_133345])).
% 27.04/17.09  tff(c_139900, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_132862, c_139886])).
% 27.04/17.09  tff(c_139912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136629, c_139900])).
% 27.04/17.09  tff(c_139913, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_89123])).
% 27.04/17.09  tff(c_139915, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_139913, c_117062])).
% 27.04/17.09  tff(c_141730, plain, (![A_7738, B_7739, C_7740, D_7741]: (k7_mcart_1(A_7738, B_7739, C_7740, D_7741)=k2_mcart_1(D_7741) | ~m1_subset_1(D_7741, k3_zfmisc_1(A_7738, B_7739, C_7740)) | k1_xboole_0=C_7740 | k1_xboole_0=B_7739 | k1_xboole_0=A_7738)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_141733, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_139915, c_141730])).
% 27.04/17.09  tff(c_141736, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_140831, c_141733])).
% 27.04/17.09  tff(c_141822, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_141736])).
% 27.04/17.09  tff(c_141935, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_141822, c_140748])).
% 27.04/17.09  tff(c_140451, plain, (![A_7655, B_7656, C_7657]: (r2_hidden(k1_mcart_1(A_7655), B_7656) | ~r2_hidden(A_7655, k2_zfmisc_1(B_7656, C_7657)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_144603, plain, (![B_7899, C_7900]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_7899, C_7900))), B_7899) | v1_xboole_0(k2_zfmisc_1(B_7899, C_7900)))), inference(resolution, [status(thm)], [c_4, c_140451])).
% 27.04/17.09  tff(c_141530, plain, (![A_7724, A_32, B_7723]: (~v1_xboole_0(A_7724) | ~r2_hidden(A_32, k2_zfmisc_1(B_7723, A_7724)))), inference(negUnitSimplification, [status(thm)], [c_38, c_141523])).
% 27.04/17.09  tff(c_144624, plain, (![A_7724, B_7723, C_7900]: (~v1_xboole_0(A_7724) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_7723, A_7724), C_7900)))), inference(resolution, [status(thm)], [c_144603, c_141530])).
% 27.04/17.09  tff(c_144741, plain, (![A_7906, B_7907, C_7908]: (~v1_xboole_0(A_7906) | v1_xboole_0(k3_zfmisc_1(B_7907, A_7906, C_7908)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_144624])).
% 27.04/17.09  tff(c_144763, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_144741, c_132861])).
% 27.04/17.09  tff(c_144776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141935, c_144763])).
% 27.04/17.09  tff(c_144777, plain, (k1_xboole_0='#skF_9' | k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_141736])).
% 27.04/17.09  tff(c_145442, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_144973, c_144777])).
% 27.04/17.09  tff(c_140117, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_139913, c_117059])).
% 27.04/17.09  tff(c_145443, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_145442, c_140117])).
% 27.04/17.09  tff(c_140898, plain, (![A_7683, B_7684, C_7685]: (k2_zfmisc_1(k2_zfmisc_1(A_7683, B_7684), C_7685)=k3_zfmisc_1(A_7683, B_7684, C_7685))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.09  tff(c_148839, plain, (![A_8123, C_8124, A_8125, B_8126]: (r2_hidden(k2_mcart_1(A_8123), C_8124) | ~r2_hidden(A_8123, k3_zfmisc_1(A_8125, B_8126, C_8124)))), inference(superposition, [status(thm), theory('equality')], [c_140898, c_52])).
% 27.04/17.09  tff(c_148856, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_132862, c_148839])).
% 27.04/17.09  tff(c_148869, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145443, c_148856])).
% 27.04/17.09  tff(c_148870, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_89023])).
% 27.04/17.09  tff(c_148968, plain, (![B_8136, A_8137]: (B_8136=A_8137 | ~r1_tarski(B_8136, A_8137) | ~r1_tarski(A_8137, B_8136))), inference(cnfTransformation, [status(thm)], [f_62])).
% 27.04/17.09  tff(c_148994, plain, (![A_8138]: (k1_xboole_0=A_8138 | ~r1_tarski(A_8138, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_148968])).
% 27.04/17.09  tff(c_149017, plain, (![A_8139]: (k1_xboole_0=A_8139 | ~v1_xboole_0(A_8139))), inference(resolution, [status(thm)], [c_89090, c_148994])).
% 27.04/17.09  tff(c_184310, plain, (![A_9905, B_9906]: (k3_xboole_0(A_9905, B_9906)=k1_xboole_0 | ~r1_xboole_0(A_9905, B_9906))), inference(resolution, [status(thm)], [c_89102, c_149017])).
% 27.04/17.09  tff(c_184335, plain, (![B_9907, A_9908]: (k3_xboole_0(B_9907, k4_xboole_0(A_9908, B_9907))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_184310])).
% 27.04/17.09  tff(c_148915, plain, (![A_8133, B_8134]: (k4_xboole_0(A_8133, k4_xboole_0(A_8133, B_8134))=k3_xboole_0(A_8133, B_8134))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.04/17.09  tff(c_148934, plain, (![A_8133, B_8134]: (r1_xboole_0(k4_xboole_0(A_8133, B_8134), k3_xboole_0(A_8133, B_8134)))), inference(superposition, [status(thm), theory('equality')], [c_148915, c_91])).
% 27.04/17.09  tff(c_184340, plain, (![B_9907, A_9908]: (r1_xboole_0(k4_xboole_0(B_9907, k4_xboole_0(A_9908, B_9907)), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_184335, c_148934])).
% 27.04/17.09  tff(c_184366, plain, (![B_9909]: (r1_xboole_0(B_9909, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_184340])).
% 27.04/17.09  tff(c_149026, plain, (![A_4744, B_4745]: (k3_xboole_0(A_4744, B_4745)=k1_xboole_0 | ~r1_xboole_0(A_4744, B_4745))), inference(resolution, [status(thm)], [c_89102, c_149017])).
% 27.04/17.09  tff(c_184385, plain, (![B_9909]: (k3_xboole_0(B_9909, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_184366, c_149026])).
% 27.04/17.09  tff(c_184472, plain, (![B_9918]: (k4_xboole_0(B_9918, k1_xboole_0)=B_9918)), inference(resolution, [status(thm)], [c_184366, c_34])).
% 27.04/17.09  tff(c_184490, plain, (![B_9918]: (k4_xboole_0(B_9918, B_9918)=k3_xboole_0(B_9918, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_184472, c_26])).
% 27.04/17.09  tff(c_184911, plain, (![B_9918]: (k4_xboole_0(B_9918, B_9918)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_184385, c_184490])).
% 27.04/17.09  tff(c_148953, plain, (![B_8135]: (k3_xboole_0(B_8135, B_8135)=B_8135)), inference(superposition, [status(thm), theory('equality')], [c_148915, c_104])).
% 27.04/17.09  tff(c_184182, plain, (![B_9889]: (~r1_xboole_0(B_9889, B_9889) | v1_xboole_0(B_9889))), inference(superposition, [status(thm), theory('equality')], [c_148953, c_89102])).
% 27.04/17.09  tff(c_184191, plain, (![A_4730]: (v1_xboole_0(A_4730) | k4_xboole_0(A_4730, A_4730)!=A_4730)), inference(resolution, [status(thm)], [c_89060, c_184182])).
% 27.04/17.09  tff(c_184978, plain, (![A_9939]: (v1_xboole_0(A_9939) | k1_xboole_0!=A_9939)), inference(demodulation, [status(thm), theory('equality')], [c_184911, c_184191])).
% 27.04/17.09  tff(c_149258, plain, (![A_8167, B_8168]: (k3_xboole_0(A_8167, B_8168)=k1_xboole_0 | ~r1_xboole_0(A_8167, B_8168))), inference(resolution, [status(thm)], [c_89102, c_149017])).
% 27.04/17.09  tff(c_149289, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_149258])).
% 27.04/17.09  tff(c_149139, plain, (![A_8156, B_8157]: (r1_xboole_0(k4_xboole_0(A_8156, B_8157), k3_xboole_0(A_8156, B_8157)))), inference(superposition, [status(thm), theory('equality')], [c_148915, c_91])).
% 27.04/17.09  tff(c_149158, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_149139])).
% 27.04/17.09  tff(c_149364, plain, (![B_8175]: (r1_xboole_0(B_8175, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_149289, c_149158])).
% 27.04/17.09  tff(c_149385, plain, (![B_8175]: (k3_xboole_0(B_8175, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_149364, c_149026])).
% 27.04/17.09  tff(c_149547, plain, (![B_8183]: (k4_xboole_0(B_8183, k1_xboole_0)=B_8183)), inference(resolution, [status(thm)], [c_149364, c_34])).
% 27.04/17.09  tff(c_149569, plain, (![B_8183]: (k4_xboole_0(B_8183, B_8183)=k3_xboole_0(B_8183, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_149547, c_26])).
% 27.04/17.09  tff(c_149931, plain, (![B_8183]: (k4_xboole_0(B_8183, B_8183)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149385, c_149569])).
% 27.04/17.09  tff(c_149067, plain, (![B_8146]: (~r1_xboole_0(B_8146, B_8146) | v1_xboole_0(B_8146))), inference(superposition, [status(thm), theory('equality')], [c_148953, c_89102])).
% 27.04/17.09  tff(c_149076, plain, (![A_4730]: (v1_xboole_0(A_4730) | k4_xboole_0(A_4730, A_4730)!=A_4730)), inference(resolution, [status(thm)], [c_89060, c_149067])).
% 27.04/17.09  tff(c_149998, plain, (![A_8203]: (v1_xboole_0(A_8203) | k1_xboole_0!=A_8203)), inference(demodulation, [status(thm), theory('equality')], [c_149931, c_149076])).
% 27.04/17.09  tff(c_148985, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_118, c_148968])).
% 27.04/17.09  tff(c_149027, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_148985])).
% 27.04/17.09  tff(c_149031, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_89090, c_149027])).
% 27.04/17.09  tff(c_150028, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_149998, c_149031])).
% 27.04/17.09  tff(c_148986, plain, ('#skF_5'='#skF_8' | ~r1_tarski('#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_117, c_148968])).
% 27.04/17.09  tff(c_149032, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_148986])).
% 27.04/17.09  tff(c_149036, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_89090, c_149032])).
% 27.04/17.09  tff(c_150027, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_149998, c_149036])).
% 27.04/17.09  tff(c_148987, plain, ('#skF_6'='#skF_9' | ~r1_tarski('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_116, c_148968])).
% 27.04/17.09  tff(c_149046, plain, (~r1_tarski('#skF_6', '#skF_9')), inference(splitLeft, [status(thm)], [c_148987])).
% 27.04/17.09  tff(c_149050, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_89090, c_149046])).
% 27.04/17.09  tff(c_150026, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_149998, c_149050])).
% 27.04/17.09  tff(c_150380, plain, (![A_8243, B_8244, C_8245, D_8246]: (k6_mcart_1(A_8243, B_8244, C_8245, D_8246)=k2_mcart_1(k1_mcart_1(D_8246)) | ~m1_subset_1(D_8246, k3_zfmisc_1(A_8243, B_8244, C_8245)) | k1_xboole_0=C_8245 | k1_xboole_0=B_8244 | k1_xboole_0=A_8243)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_150383, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_150380])).
% 27.04/17.09  tff(c_150386, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_150028, c_150027, c_150026, c_150383])).
% 27.04/17.09  tff(c_149446, plain, (![A_8178, B_8179, C_8180]: (k2_zfmisc_1(k2_zfmisc_1(A_8178, B_8179), C_8180)=k3_zfmisc_1(A_8178, B_8179, C_8180))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.09  tff(c_155270, plain, (![A_8458, A_8459, B_8460, C_8461]: (r2_hidden(k1_mcart_1(A_8458), k2_zfmisc_1(A_8459, B_8460)) | ~r2_hidden(A_8458, k3_zfmisc_1(A_8459, B_8460, C_8461)))), inference(superposition, [status(thm), theory('equality')], [c_149446, c_54])).
% 27.04/17.09  tff(c_155314, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_64, c_155270])).
% 27.04/17.09  tff(c_155382, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_155314, c_52])).
% 27.04/17.09  tff(c_155401, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_150386, c_155382])).
% 27.04/17.09  tff(c_155403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148870, c_155401])).
% 27.04/17.09  tff(c_155404, plain, ('#skF_6'='#skF_9'), inference(splitRight, [status(thm)], [c_148987])).
% 27.04/17.09  tff(c_155407, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_155404, c_148870])).
% 27.04/17.09  tff(c_155589, plain, (![A_8483, B_8484]: (k3_xboole_0(A_8483, B_8484)=k1_xboole_0 | ~r1_xboole_0(A_8483, B_8484))), inference(resolution, [status(thm)], [c_89102, c_149017])).
% 27.04/17.09  tff(c_155614, plain, (![B_8485, A_8486]: (k3_xboole_0(B_8485, k4_xboole_0(A_8486, B_8485))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_155589])).
% 27.04/17.09  tff(c_155619, plain, (![B_8485, A_8486]: (r1_xboole_0(k4_xboole_0(B_8485, k4_xboole_0(A_8486, B_8485)), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_155614, c_148934])).
% 27.04/17.09  tff(c_155645, plain, (![B_8487]: (r1_xboole_0(B_8487, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_155619])).
% 27.04/17.09  tff(c_155664, plain, (![B_8487]: (k3_xboole_0(B_8487, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_155645, c_149026])).
% 27.04/17.09  tff(c_155857, plain, (![B_8496]: (k4_xboole_0(B_8496, k1_xboole_0)=B_8496)), inference(resolution, [status(thm)], [c_155645, c_34])).
% 27.04/17.09  tff(c_155879, plain, (![B_8496]: (k4_xboole_0(B_8496, B_8496)=k3_xboole_0(B_8496, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_155857, c_26])).
% 27.04/17.09  tff(c_155905, plain, (![B_8496]: (k4_xboole_0(B_8496, B_8496)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_155664, c_155879])).
% 27.04/17.09  tff(c_155423, plain, (![B_8463]: (~r1_xboole_0(B_8463, B_8463) | v1_xboole_0(B_8463))), inference(superposition, [status(thm), theory('equality')], [c_148953, c_89102])).
% 27.04/17.09  tff(c_155433, plain, (![B_30]: (v1_xboole_0(B_30) | k4_xboole_0(B_30, B_30)!=B_30)), inference(resolution, [status(thm)], [c_36, c_155423])).
% 27.04/17.09  tff(c_156073, plain, (![B_8503]: (v1_xboole_0(B_8503) | k1_xboole_0!=B_8503)), inference(demodulation, [status(thm), theory('equality')], [c_155905, c_155433])).
% 27.04/17.09  tff(c_156099, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_156073, c_149031])).
% 27.04/17.09  tff(c_156098, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_156073, c_149036])).
% 27.04/17.09  tff(c_148871, plain, (r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_89023])).
% 27.04/17.09  tff(c_148875, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_148871, c_2])).
% 27.04/17.09  tff(c_156101, plain, (k1_xboole_0!='#skF_9'), inference(resolution, [status(thm)], [c_156073, c_148875])).
% 27.04/17.09  tff(c_155410, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_155404, c_66])).
% 27.04/17.09  tff(c_156857, plain, (![A_8571, B_8572, C_8573, D_8574]: (k6_mcart_1(A_8571, B_8572, C_8573, D_8574)=k2_mcart_1(k1_mcart_1(D_8574)) | ~m1_subset_1(D_8574, k3_zfmisc_1(A_8571, B_8572, C_8573)) | k1_xboole_0=C_8573 | k1_xboole_0=B_8572 | k1_xboole_0=A_8571)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_156860, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_155410, c_156857])).
% 27.04/17.09  tff(c_156863, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_156099, c_156098, c_156101, c_156860])).
% 27.04/17.09  tff(c_155557, plain, (![A_8480, B_8481, C_8482]: (k2_zfmisc_1(k2_zfmisc_1(A_8480, B_8481), C_8482)=k3_zfmisc_1(A_8480, B_8481, C_8482))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.09  tff(c_161337, plain, (![A_8763, A_8764, B_8765, C_8766]: (r2_hidden(k1_mcart_1(A_8763), k2_zfmisc_1(A_8764, B_8765)) | ~r2_hidden(A_8763, k3_zfmisc_1(A_8764, B_8765, C_8766)))), inference(superposition, [status(thm), theory('equality')], [c_155557, c_54])).
% 27.04/17.09  tff(c_161382, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_64, c_161337])).
% 27.04/17.09  tff(c_161396, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_161382, c_52])).
% 27.04/17.09  tff(c_161415, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_156863, c_161396])).
% 27.04/17.09  tff(c_161417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155407, c_161415])).
% 27.04/17.09  tff(c_161418, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_148986])).
% 27.04/17.09  tff(c_161421, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_161418, c_148870])).
% 27.04/17.09  tff(c_161629, plain, (![A_8791, B_8792]: (k3_xboole_0(A_8791, B_8792)=k1_xboole_0 | ~r1_xboole_0(A_8791, B_8792))), inference(resolution, [status(thm)], [c_89102, c_149017])).
% 27.04/17.09  tff(c_161656, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_161629])).
% 27.04/17.09  tff(c_161550, plain, (![A_8781, B_8782]: (r1_xboole_0(k4_xboole_0(A_8781, B_8782), k3_xboole_0(A_8781, B_8782)))), inference(superposition, [status(thm), theory('equality')], [c_148915, c_91])).
% 27.04/17.09  tff(c_161567, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_161550])).
% 27.04/17.09  tff(c_161690, plain, (![B_8795]: (r1_xboole_0(B_8795, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_161656, c_161567])).
% 27.04/17.09  tff(c_161711, plain, (![B_8795]: (k3_xboole_0(B_8795, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_161690, c_149026])).
% 27.04/17.09  tff(c_161795, plain, (![B_8802]: (k4_xboole_0(B_8802, k1_xboole_0)=B_8802)), inference(resolution, [status(thm)], [c_161690, c_34])).
% 27.04/17.09  tff(c_161813, plain, (![B_8802]: (k4_xboole_0(B_8802, B_8802)=k3_xboole_0(B_8802, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_161795, c_26])).
% 27.04/17.09  tff(c_162203, plain, (![B_8802]: (k4_xboole_0(B_8802, B_8802)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161711, c_161813])).
% 27.04/17.09  tff(c_161442, plain, (![B_8767]: (~r1_xboole_0(B_8767, B_8767) | v1_xboole_0(B_8767))), inference(superposition, [status(thm), theory('equality')], [c_148953, c_89102])).
% 27.04/17.09  tff(c_161452, plain, (![B_30]: (v1_xboole_0(B_30) | k4_xboole_0(B_30, B_30)!=B_30)), inference(resolution, [status(thm)], [c_36, c_161442])).
% 27.04/17.09  tff(c_162305, plain, (![B_8823]: (v1_xboole_0(B_8823) | k1_xboole_0!=B_8823)), inference(demodulation, [status(thm), theory('equality')], [c_162203, c_161452])).
% 27.04/17.09  tff(c_162331, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_162305, c_149031])).
% 27.04/17.09  tff(c_161437, plain, (~r1_tarski('#skF_6', '#skF_9')), inference(splitLeft, [status(thm)], [c_148987])).
% 27.04/17.09  tff(c_161441, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_89090, c_161437])).
% 27.04/17.09  tff(c_162330, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_162305, c_161441])).
% 27.04/17.09  tff(c_161424, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_161418, c_66])).
% 27.04/17.09  tff(c_162505, plain, (![A_8841, B_8842, C_8843, D_8844]: (k7_mcart_1(A_8841, B_8842, C_8843, D_8844)=k2_mcart_1(D_8844) | ~m1_subset_1(D_8844, k3_zfmisc_1(A_8841, B_8842, C_8843)) | k1_xboole_0=C_8843 | k1_xboole_0=B_8842 | k1_xboole_0=A_8841)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_162508, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_161424, c_162505])).
% 27.04/17.09  tff(c_162511, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_162331, c_162330, c_162508])).
% 27.04/17.09  tff(c_162578, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_162511])).
% 27.04/17.09  tff(c_162204, plain, (![B_30]: (v1_xboole_0(B_30) | k1_xboole_0!=B_30)), inference(demodulation, [status(thm), theory('equality')], [c_162203, c_161452])).
% 27.04/17.09  tff(c_163064, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_162578, c_162204])).
% 27.04/17.09  tff(c_161946, plain, (![A_8805, B_8806, C_8807]: (r2_hidden(k1_mcart_1(A_8805), B_8806) | ~r2_hidden(A_8805, k2_zfmisc_1(B_8806, C_8807)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_165883, plain, (![B_9019, C_9020]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_9019, C_9020))), B_9019) | v1_xboole_0(k2_zfmisc_1(B_9019, C_9020)))), inference(resolution, [status(thm)], [c_4, c_161946])).
% 27.04/17.09  tff(c_162379, plain, (![C_8829, B_8830, A_8831]: (v1_xboole_0(C_8829) | ~m1_subset_1(C_8829, k1_zfmisc_1(k2_zfmisc_1(B_8830, A_8831))) | ~v1_xboole_0(A_8831))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.09  tff(c_162386, plain, (![A_32, A_8831, B_8830]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_8831) | ~r2_hidden(A_32, k2_zfmisc_1(B_8830, A_8831)))), inference(resolution, [status(thm)], [c_40, c_162379])).
% 27.04/17.09  tff(c_162393, plain, (![A_8831, A_32, B_8830]: (~v1_xboole_0(A_8831) | ~r2_hidden(A_32, k2_zfmisc_1(B_8830, A_8831)))), inference(negUnitSimplification, [status(thm)], [c_38, c_162386])).
% 27.04/17.09  tff(c_165900, plain, (![A_8831, B_8830, C_9020]: (~v1_xboole_0(A_8831) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_8830, A_8831), C_9020)))), inference(resolution, [status(thm)], [c_165883, c_162393])).
% 27.04/17.09  tff(c_166021, plain, (![A_9026, B_9027, C_9028]: (~v1_xboole_0(A_9026) | v1_xboole_0(k3_zfmisc_1(B_9027, A_9026, C_9028)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_165900])).
% 27.04/17.09  tff(c_166043, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_166021, c_82])).
% 27.04/17.09  tff(c_166056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_163064, c_166043])).
% 27.04/17.09  tff(c_166058, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_162511])).
% 27.04/17.09  tff(c_166161, plain, (![A_9041, B_9042, C_9043, D_9044]: (k6_mcart_1(A_9041, B_9042, C_9043, D_9044)=k2_mcart_1(k1_mcart_1(D_9044)) | ~m1_subset_1(D_9044, k3_zfmisc_1(A_9041, B_9042, C_9043)) | k1_xboole_0=C_9043 | k1_xboole_0=B_9042 | k1_xboole_0=A_9041)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_166164, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_161424, c_166161])).
% 27.04/17.09  tff(c_166167, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_162331, c_166058, c_162330, c_166164])).
% 27.04/17.09  tff(c_171941, plain, (![A_9297, A_9298, B_9299, C_9300]: (r2_hidden(k1_mcart_1(A_9297), k2_zfmisc_1(A_9298, B_9299)) | ~r2_hidden(A_9297, k3_zfmisc_1(A_9298, B_9299, C_9300)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_161946])).
% 27.04/17.09  tff(c_171989, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_64, c_171941])).
% 27.04/17.09  tff(c_172018, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_171989, c_52])).
% 27.04/17.09  tff(c_172036, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_166167, c_172018])).
% 27.04/17.09  tff(c_172038, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161421, c_172036])).
% 27.04/17.09  tff(c_172039, plain, ('#skF_6'='#skF_9'), inference(splitRight, [status(thm)], [c_148987])).
% 27.04/17.09  tff(c_172178, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_172039, c_161421])).
% 27.04/17.09  tff(c_172219, plain, (![A_9322, B_9323]: (k3_xboole_0(A_9322, B_9323)=k1_xboole_0 | ~r1_xboole_0(A_9322, B_9323))), inference(resolution, [status(thm)], [c_89102, c_149017])).
% 27.04/17.09  tff(c_172246, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_172219])).
% 27.04/17.09  tff(c_172098, plain, (![A_9309, B_9310]: (r1_xboole_0(k3_xboole_0(A_9309, B_9310), k4_xboole_0(A_9309, B_9310)))), inference(superposition, [status(thm), theory('equality')], [c_148915, c_32])).
% 27.04/17.09  tff(c_172154, plain, (![A_9315, B_9316]: (r1_xboole_0(k4_xboole_0(A_9315, B_9316), k3_xboole_0(A_9315, B_9316)))), inference(resolution, [status(thm)], [c_172098, c_12])).
% 27.04/17.09  tff(c_172171, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_172154])).
% 27.04/17.09  tff(c_172345, plain, (![B_9332]: (r1_xboole_0(B_9332, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_172246, c_172171])).
% 27.04/17.09  tff(c_172368, plain, (![B_9332]: (k3_xboole_0(B_9332, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_172345, c_149026])).
% 27.04/17.09  tff(c_172480, plain, (![B_9339]: (k4_xboole_0(B_9339, k1_xboole_0)=B_9339)), inference(resolution, [status(thm)], [c_172345, c_34])).
% 27.04/17.09  tff(c_172501, plain, (![B_9339]: (k4_xboole_0(B_9339, B_9339)=k3_xboole_0(B_9339, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_172480, c_26])).
% 27.04/17.09  tff(c_172523, plain, (![B_9339]: (k4_xboole_0(B_9339, B_9339)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_172368, c_172501])).
% 27.04/17.09  tff(c_172054, plain, (![B_9301]: (~r1_xboole_0(B_9301, B_9301) | v1_xboole_0(B_9301))), inference(superposition, [status(thm), theory('equality')], [c_148953, c_89102])).
% 27.04/17.09  tff(c_172063, plain, (![A_4730]: (v1_xboole_0(A_4730) | k4_xboole_0(A_4730, A_4730)!=A_4730)), inference(resolution, [status(thm)], [c_89060, c_172054])).
% 27.04/17.09  tff(c_172736, plain, (![A_9346]: (v1_xboole_0(A_9346) | k1_xboole_0!=A_9346)), inference(demodulation, [status(thm), theory('equality')], [c_172523, c_172063])).
% 27.04/17.09  tff(c_172758, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_172736, c_149031])).
% 27.04/17.09  tff(c_172760, plain, (k1_xboole_0!='#skF_9'), inference(resolution, [status(thm)], [c_172736, c_148875])).
% 27.04/17.09  tff(c_172078, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_172039, c_161424])).
% 27.04/17.09  tff(c_173258, plain, (![A_9392, B_9393, C_9394, D_9395]: (k7_mcart_1(A_9392, B_9393, C_9394, D_9395)=k2_mcart_1(D_9395) | ~m1_subset_1(D_9395, k3_zfmisc_1(A_9392, B_9393, C_9394)) | k1_xboole_0=C_9394 | k1_xboole_0=B_9393 | k1_xboole_0=A_9392)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_173261, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_172078, c_173258])).
% 27.04/17.09  tff(c_173264, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_172758, c_172760, c_173261])).
% 27.04/17.09  tff(c_173369, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_173264])).
% 27.04/17.09  tff(c_172658, plain, (![A_4730]: (v1_xboole_0(A_4730) | k1_xboole_0!=A_4730)), inference(demodulation, [status(thm), theory('equality')], [c_172523, c_172063])).
% 27.04/17.09  tff(c_173715, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_173369, c_172658])).
% 27.04/17.09  tff(c_172088, plain, (![A_9305, B_9306, C_9307]: (r2_hidden(k1_mcart_1(A_9305), B_9306) | ~r2_hidden(A_9305, k2_zfmisc_1(B_9306, C_9307)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_176771, plain, (![B_9574, C_9575]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_9574, C_9575))), B_9574) | v1_xboole_0(k2_zfmisc_1(B_9574, C_9575)))), inference(resolution, [status(thm)], [c_4, c_172088])).
% 27.04/17.09  tff(c_172860, plain, (![C_9354, B_9355, A_9356]: (v1_xboole_0(C_9354) | ~m1_subset_1(C_9354, k1_zfmisc_1(k2_zfmisc_1(B_9355, A_9356))) | ~v1_xboole_0(A_9356))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.09  tff(c_172867, plain, (![A_32, A_9356, B_9355]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_9356) | ~r2_hidden(A_32, k2_zfmisc_1(B_9355, A_9356)))), inference(resolution, [status(thm)], [c_40, c_172860])).
% 27.04/17.09  tff(c_172874, plain, (![A_9356, A_32, B_9355]: (~v1_xboole_0(A_9356) | ~r2_hidden(A_32, k2_zfmisc_1(B_9355, A_9356)))), inference(negUnitSimplification, [status(thm)], [c_38, c_172867])).
% 27.04/17.09  tff(c_176792, plain, (![A_9356, B_9355, C_9575]: (~v1_xboole_0(A_9356) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_9355, A_9356), C_9575)))), inference(resolution, [status(thm)], [c_176771, c_172874])).
% 27.04/17.09  tff(c_176927, plain, (![A_9581, B_9582, C_9583]: (~v1_xboole_0(A_9581) | v1_xboole_0(k3_zfmisc_1(B_9582, A_9581, C_9583)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_176792])).
% 27.04/17.09  tff(c_176955, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_176927, c_82])).
% 27.04/17.09  tff(c_176971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173715, c_176955])).
% 27.04/17.09  tff(c_176973, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_173264])).
% 27.04/17.09  tff(c_177054, plain, (![A_9590, B_9591, C_9592, D_9593]: (k6_mcart_1(A_9590, B_9591, C_9592, D_9593)=k2_mcart_1(k1_mcart_1(D_9593)) | ~m1_subset_1(D_9593, k3_zfmisc_1(A_9590, B_9591, C_9592)) | k1_xboole_0=C_9592 | k1_xboole_0=B_9591 | k1_xboole_0=A_9590)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_177057, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_172078, c_177054])).
% 27.04/17.09  tff(c_177060, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_172758, c_176973, c_172760, c_177057])).
% 27.04/17.09  tff(c_172179, plain, (![A_9317, B_9318, C_9319]: (k2_zfmisc_1(k2_zfmisc_1(A_9317, B_9318), C_9319)=k3_zfmisc_1(A_9317, B_9318, C_9319))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.09  tff(c_184046, plain, (![A_9882, A_9883, B_9884, C_9885]: (r2_hidden(k1_mcart_1(A_9882), k2_zfmisc_1(A_9883, B_9884)) | ~r2_hidden(A_9882, k3_zfmisc_1(A_9883, B_9884, C_9885)))), inference(superposition, [status(thm), theory('equality')], [c_172179, c_54])).
% 27.04/17.09  tff(c_184098, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_64, c_184046])).
% 27.04/17.09  tff(c_184112, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_184098, c_52])).
% 27.04/17.09  tff(c_184131, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_177060, c_184112])).
% 27.04/17.09  tff(c_184133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172178, c_184131])).
% 27.04/17.09  tff(c_184134, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_148985])).
% 27.04/17.09  tff(c_184136, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_184134, c_89064])).
% 27.04/17.09  tff(c_185006, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_184978, c_184136])).
% 27.04/17.09  tff(c_184173, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_148986])).
% 27.04/17.09  tff(c_184177, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_89090, c_184173])).
% 27.04/17.09  tff(c_185003, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_184978, c_184177])).
% 27.04/17.09  tff(c_184153, plain, (~r1_tarski('#skF_6', '#skF_9')), inference(splitLeft, [status(thm)], [c_148987])).
% 27.04/17.09  tff(c_184157, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_89090, c_184153])).
% 27.04/17.09  tff(c_185004, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_184978, c_184157])).
% 27.04/17.09  tff(c_185581, plain, (![A_9995, B_9996, C_9997, D_9998]: (k6_mcart_1(A_9995, B_9996, C_9997, D_9998)=k2_mcart_1(k1_mcart_1(D_9998)) | ~m1_subset_1(D_9998, k3_zfmisc_1(A_9995, B_9996, C_9997)) | k1_xboole_0=C_9997 | k1_xboole_0=B_9996 | k1_xboole_0=A_9995)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_185584, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_66, c_185581])).
% 27.04/17.09  tff(c_185587, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_185006, c_185003, c_185004, c_185584])).
% 27.04/17.09  tff(c_184140, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_184134, c_64])).
% 27.04/17.09  tff(c_184461, plain, (![A_9915, B_9916, C_9917]: (r2_hidden(k1_mcart_1(A_9915), B_9916) | ~r2_hidden(A_9915, k2_zfmisc_1(B_9916, C_9917)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_190327, plain, (![A_10198, A_10199, B_10200, C_10201]: (r2_hidden(k1_mcart_1(A_10198), k2_zfmisc_1(A_10199, B_10200)) | ~r2_hidden(A_10198, k3_zfmisc_1(A_10199, B_10200, C_10201)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_184461])).
% 27.04/17.09  tff(c_190373, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_184140, c_190327])).
% 27.04/17.09  tff(c_190393, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_190373, c_52])).
% 27.04/17.09  tff(c_190411, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_185587, c_190393])).
% 27.04/17.09  tff(c_190413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148870, c_190411])).
% 27.04/17.09  tff(c_190414, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_148986])).
% 27.04/17.09  tff(c_190417, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_190414, c_148870])).
% 27.04/17.09  tff(c_190630, plain, (![A_10226, B_10227]: (k3_xboole_0(A_10226, B_10227)=k1_xboole_0 | ~r1_xboole_0(A_10226, B_10227))), inference(resolution, [status(thm)], [c_89102, c_149017])).
% 27.04/17.09  tff(c_190661, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_190630])).
% 27.04/17.09  tff(c_190481, plain, (![A_10210, B_10211]: (r1_xboole_0(k3_xboole_0(A_10210, B_10211), k4_xboole_0(A_10210, B_10211)))), inference(superposition, [status(thm), theory('equality')], [c_148915, c_32])).
% 27.04/17.09  tff(c_190508, plain, (![A_10212, B_10213]: (r1_xboole_0(k4_xboole_0(A_10212, B_10213), k3_xboole_0(A_10212, B_10213)))), inference(resolution, [status(thm)], [c_190481, c_12])).
% 27.04/17.09  tff(c_190525, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_190508])).
% 27.04/17.09  tff(c_190724, plain, (![B_10231]: (r1_xboole_0(B_10231, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_190661, c_190525])).
% 27.04/17.09  tff(c_190743, plain, (![B_10231]: (k3_xboole_0(B_10231, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_190724, c_149026])).
% 27.04/17.09  tff(c_190813, plain, (![B_10237]: (k4_xboole_0(B_10237, k1_xboole_0)=B_10237)), inference(resolution, [status(thm)], [c_190724, c_34])).
% 27.04/17.09  tff(c_190831, plain, (![B_10237]: (k4_xboole_0(B_10237, B_10237)=k3_xboole_0(B_10237, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_190813, c_26])).
% 27.04/17.09  tff(c_191295, plain, (![B_10237]: (k4_xboole_0(B_10237, B_10237)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_190743, c_190831])).
% 27.04/17.09  tff(c_190432, plain, (![B_10202]: (~r1_xboole_0(B_10202, B_10202) | v1_xboole_0(B_10202))), inference(superposition, [status(thm), theory('equality')], [c_148953, c_89102])).
% 27.04/17.09  tff(c_190441, plain, (![A_4730]: (v1_xboole_0(A_4730) | k4_xboole_0(A_4730, A_4730)!=A_4730)), inference(resolution, [status(thm)], [c_89060, c_190432])).
% 27.04/17.09  tff(c_191362, plain, (![A_10262]: (v1_xboole_0(A_10262) | k1_xboole_0!=A_10262)), inference(demodulation, [status(thm), theory('equality')], [c_191295, c_190441])).
% 27.04/17.09  tff(c_191386, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_191362, c_184136])).
% 27.04/17.09  tff(c_191384, plain, (k1_xboole_0!='#skF_6'), inference(resolution, [status(thm)], [c_191362, c_184157])).
% 27.04/17.09  tff(c_190419, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_190414, c_66])).
% 27.04/17.09  tff(c_191586, plain, (![A_10280, B_10281, C_10282, D_10283]: (k7_mcart_1(A_10280, B_10281, C_10282, D_10283)=k2_mcart_1(D_10283) | ~m1_subset_1(D_10283, k3_zfmisc_1(A_10280, B_10281, C_10282)) | k1_xboole_0=C_10282 | k1_xboole_0=B_10281 | k1_xboole_0=A_10280)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_191589, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_190419, c_191586])).
% 27.04/17.09  tff(c_191592, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_191386, c_191384, c_191589])).
% 27.04/17.09  tff(c_191665, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_191592])).
% 27.04/17.09  tff(c_191296, plain, (![A_4730]: (v1_xboole_0(A_4730) | k1_xboole_0!=A_4730)), inference(demodulation, [status(thm), theory('equality')], [c_191295, c_190441])).
% 27.04/17.09  tff(c_192192, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_191665, c_191296])).
% 27.04/17.09  tff(c_190764, plain, (![A_10233, B_10234, C_10235]: (r2_hidden(k1_mcart_1(A_10233), B_10234) | ~r2_hidden(A_10233, k2_zfmisc_1(B_10234, C_10235)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_195536, plain, (![B_10487, C_10488]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_10487, C_10488))), B_10487) | v1_xboole_0(k2_zfmisc_1(B_10487, C_10488)))), inference(resolution, [status(thm)], [c_4, c_190764])).
% 27.04/17.09  tff(c_191106, plain, (![C_10247, B_10248, A_10249]: (v1_xboole_0(C_10247) | ~m1_subset_1(C_10247, k1_zfmisc_1(k2_zfmisc_1(B_10248, A_10249))) | ~v1_xboole_0(A_10249))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.09  tff(c_191113, plain, (![A_32, A_10249, B_10248]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_10249) | ~r2_hidden(A_32, k2_zfmisc_1(B_10248, A_10249)))), inference(resolution, [status(thm)], [c_40, c_191106])).
% 27.04/17.09  tff(c_191120, plain, (![A_10249, A_32, B_10248]: (~v1_xboole_0(A_10249) | ~r2_hidden(A_32, k2_zfmisc_1(B_10248, A_10249)))), inference(negUnitSimplification, [status(thm)], [c_38, c_191113])).
% 27.04/17.09  tff(c_195549, plain, (![A_10249, B_10248, C_10488]: (~v1_xboole_0(A_10249) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(B_10248, A_10249), C_10488)))), inference(resolution, [status(thm)], [c_195536, c_191120])).
% 27.04/17.09  tff(c_196094, plain, (![A_10506, B_10507, C_10508]: (~v1_xboole_0(A_10506) | v1_xboole_0(k3_zfmisc_1(B_10507, A_10506, C_10508)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_195549])).
% 27.04/17.09  tff(c_184139, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_184134, c_82])).
% 27.04/17.09  tff(c_196122, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_196094, c_184139])).
% 27.04/17.09  tff(c_196141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_192192, c_196122])).
% 27.04/17.09  tff(c_196143, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_191592])).
% 27.04/17.09  tff(c_196255, plain, (![A_10520, B_10521, C_10522, D_10523]: (k6_mcart_1(A_10520, B_10521, C_10522, D_10523)=k2_mcart_1(k1_mcart_1(D_10523)) | ~m1_subset_1(D_10523, k3_zfmisc_1(A_10520, B_10521, C_10522)) | k1_xboole_0=C_10522 | k1_xboole_0=B_10521 | k1_xboole_0=A_10520)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_196258, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_190419, c_196255])).
% 27.04/17.09  tff(c_196261, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_191386, c_196143, c_191384, c_196258])).
% 27.04/17.09  tff(c_201069, plain, (![A_10751, A_10752, B_10753, C_10754]: (r2_hidden(k1_mcart_1(A_10751), k2_zfmisc_1(A_10752, B_10753)) | ~r2_hidden(A_10751, k3_zfmisc_1(A_10752, B_10753, C_10754)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_190764])).
% 27.04/17.09  tff(c_201112, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_184140, c_201069])).
% 27.04/17.09  tff(c_201132, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_201112, c_52])).
% 27.04/17.09  tff(c_201150, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_196261, c_201132])).
% 27.04/17.09  tff(c_201152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190417, c_201150])).
% 27.04/17.09  tff(c_201153, plain, ('#skF_6'='#skF_9'), inference(splitRight, [status(thm)], [c_148987])).
% 27.04/17.09  tff(c_201156, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_201153, c_148870])).
% 27.04/17.09  tff(c_201372, plain, (![A_10781, B_10782]: (k3_xboole_0(A_10781, B_10782)=k1_xboole_0 | ~r1_xboole_0(A_10781, B_10782))), inference(resolution, [status(thm)], [c_89102, c_149017])).
% 27.04/17.09  tff(c_201403, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_201372])).
% 27.04/17.09  tff(c_201250, plain, (![A_10765, B_10766]: (r1_xboole_0(k4_xboole_0(A_10765, B_10766), k3_xboole_0(A_10765, B_10766)))), inference(superposition, [status(thm), theory('equality')], [c_148915, c_91])).
% 27.04/17.09  tff(c_201267, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_201250])).
% 27.04/17.09  tff(c_201482, plain, (![B_10789]: (r1_xboole_0(B_10789, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_201403, c_201267])).
% 27.04/17.09  tff(c_201501, plain, (![B_10789]: (k3_xboole_0(B_10789, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_201482, c_149026])).
% 27.04/17.09  tff(c_201748, plain, (![B_10799]: (k4_xboole_0(B_10799, k1_xboole_0)=B_10799)), inference(resolution, [status(thm)], [c_201482, c_34])).
% 27.04/17.09  tff(c_201770, plain, (![B_10799]: (k4_xboole_0(B_10799, B_10799)=k3_xboole_0(B_10799, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_201748, c_26])).
% 27.04/17.09  tff(c_201797, plain, (![B_10799]: (k4_xboole_0(B_10799, B_10799)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_201501, c_201770])).
% 27.04/17.09  tff(c_201176, plain, (![B_10755]: (~r1_xboole_0(B_10755, B_10755) | v1_xboole_0(B_10755))), inference(superposition, [status(thm), theory('equality')], [c_148953, c_89102])).
% 27.04/17.09  tff(c_201186, plain, (![B_30]: (v1_xboole_0(B_30) | k4_xboole_0(B_30, B_30)!=B_30)), inference(resolution, [status(thm)], [c_36, c_201176])).
% 27.04/17.09  tff(c_201885, plain, (![B_10804]: (v1_xboole_0(B_10804) | k1_xboole_0!=B_10804)), inference(demodulation, [status(thm), theory('equality')], [c_201797, c_201186])).
% 27.04/17.09  tff(c_201909, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_201885, c_184136])).
% 27.04/17.09  tff(c_201171, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_148986])).
% 27.04/17.09  tff(c_201175, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_89090, c_201171])).
% 27.04/17.09  tff(c_201907, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_201885, c_201175])).
% 27.04/17.09  tff(c_201911, plain, (k1_xboole_0!='#skF_9'), inference(resolution, [status(thm)], [c_201885, c_148875])).
% 27.04/17.09  tff(c_201158, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_201153, c_66])).
% 27.04/17.09  tff(c_202770, plain, (![A_10880, B_10881, C_10882, D_10883]: (k6_mcart_1(A_10880, B_10881, C_10882, D_10883)=k2_mcart_1(k1_mcart_1(D_10883)) | ~m1_subset_1(D_10883, k3_zfmisc_1(A_10880, B_10881, C_10882)) | k1_xboole_0=C_10882 | k1_xboole_0=B_10881 | k1_xboole_0=A_10880)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_202773, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_201158, c_202770])).
% 27.04/17.09  tff(c_202776, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_201909, c_201907, c_201911, c_202773])).
% 27.04/17.09  tff(c_201309, plain, (![A_10772, B_10773, C_10774]: (k2_zfmisc_1(k2_zfmisc_1(A_10772, B_10773), C_10774)=k3_zfmisc_1(A_10772, B_10773, C_10774))), inference(cnfTransformation, [status(thm)], [f_113])).
% 27.04/17.09  tff(c_207141, plain, (![A_11083, A_11084, B_11085, C_11086]: (r2_hidden(k1_mcart_1(A_11083), k2_zfmisc_1(A_11084, B_11085)) | ~r2_hidden(A_11083, k3_zfmisc_1(A_11084, B_11085, C_11086)))), inference(superposition, [status(thm), theory('equality')], [c_201309, c_54])).
% 27.04/17.09  tff(c_207180, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_184140, c_207141])).
% 27.04/17.09  tff(c_207198, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_207180, c_52])).
% 27.04/17.09  tff(c_207216, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_202776, c_207198])).
% 27.04/17.09  tff(c_207218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201156, c_207216])).
% 27.04/17.09  tff(c_207219, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_148986])).
% 27.04/17.09  tff(c_207340, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_207219, c_201156])).
% 27.04/17.09  tff(c_207399, plain, (![A_11108, B_11109]: (k3_xboole_0(A_11108, B_11109)=k1_xboole_0 | ~r1_xboole_0(A_11108, B_11109))), inference(resolution, [status(thm)], [c_89102, c_149017])).
% 27.04/17.09  tff(c_207426, plain, (![B_28, A_27]: (k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91, c_207399])).
% 27.04/17.09  tff(c_207288, plain, (![A_11095, B_11096]: (r1_xboole_0(k3_xboole_0(A_11095, B_11096), k4_xboole_0(A_11095, B_11096)))), inference(superposition, [status(thm), theory('equality')], [c_148915, c_32])).
% 27.04/17.09  tff(c_207341, plain, (![A_11101, B_11102]: (r1_xboole_0(k4_xboole_0(A_11101, B_11102), k3_xboole_0(A_11101, B_11102)))), inference(resolution, [status(thm)], [c_207288, c_12])).
% 27.04/17.09  tff(c_207358, plain, (![B_28, A_27]: (r1_xboole_0(B_28, k3_xboole_0(B_28, k4_xboole_0(A_27, B_28))))), inference(superposition, [status(thm), theory('equality')], [c_104, c_207341])).
% 27.04/17.09  tff(c_207519, plain, (![B_11118]: (r1_xboole_0(B_11118, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_207426, c_207358])).
% 27.04/17.09  tff(c_207538, plain, (![B_11118]: (k3_xboole_0(B_11118, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_207519, c_149026])).
% 27.04/17.09  tff(c_207602, plain, (![B_11123]: (k4_xboole_0(B_11123, k1_xboole_0)=B_11123)), inference(resolution, [status(thm)], [c_207519, c_34])).
% 27.04/17.09  tff(c_207623, plain, (![B_11123]: (k4_xboole_0(B_11123, B_11123)=k3_xboole_0(B_11123, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_207602, c_26])).
% 27.04/17.09  tff(c_208019, plain, (![B_11123]: (k4_xboole_0(B_11123, B_11123)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_207538, c_207623])).
% 27.04/17.09  tff(c_207234, plain, (![B_11087]: (~r1_xboole_0(B_11087, B_11087) | v1_xboole_0(B_11087))), inference(superposition, [status(thm), theory('equality')], [c_148953, c_89102])).
% 27.04/17.09  tff(c_207244, plain, (![B_30]: (v1_xboole_0(B_30) | k4_xboole_0(B_30, B_30)!=B_30)), inference(resolution, [status(thm)], [c_36, c_207234])).
% 27.04/17.09  tff(c_208086, plain, (![B_11143]: (v1_xboole_0(B_11143) | k1_xboole_0!=B_11143)), inference(demodulation, [status(thm), theory('equality')], [c_208019, c_207244])).
% 27.04/17.09  tff(c_208106, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_208086, c_184136])).
% 27.04/17.09  tff(c_208108, plain, (k1_xboole_0!='#skF_9'), inference(resolution, [status(thm)], [c_208086, c_148875])).
% 27.04/17.09  tff(c_207262, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_207219, c_201158])).
% 27.04/17.09  tff(c_208385, plain, (![A_11171, B_11172, C_11173, D_11174]: (k7_mcart_1(A_11171, B_11172, C_11173, D_11174)=k2_mcart_1(D_11174) | ~m1_subset_1(D_11174, k3_zfmisc_1(A_11171, B_11172, C_11173)) | k1_xboole_0=C_11173 | k1_xboole_0=B_11172 | k1_xboole_0=A_11171)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_208388, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_207262, c_208385])).
% 27.04/17.09  tff(c_208391, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_208106, c_208108, c_208388])).
% 27.04/17.09  tff(c_208479, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_208391])).
% 27.04/17.09  tff(c_208020, plain, (![B_30]: (v1_xboole_0(B_30) | k1_xboole_0!=B_30)), inference(demodulation, [status(thm), theory('equality')], [c_208019, c_207244])).
% 27.04/17.09  tff(c_208496, plain, (![B_30]: (v1_xboole_0(B_30) | B_30!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_208479, c_208020])).
% 27.04/17.09  tff(c_208110, plain, (![C_11144, B_11145, A_11146]: (v1_xboole_0(C_11144) | ~m1_subset_1(C_11144, k1_zfmisc_1(k2_zfmisc_1(B_11145, A_11146))) | ~v1_xboole_0(A_11146))), inference(cnfTransformation, [status(thm)], [f_111])).
% 27.04/17.09  tff(c_208117, plain, (![A_32, A_11146, B_11145]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_11146) | ~r2_hidden(A_32, k2_zfmisc_1(B_11145, A_11146)))), inference(resolution, [status(thm)], [c_40, c_208110])).
% 27.04/17.09  tff(c_208430, plain, (![A_11177, A_11178, B_11179]: (~v1_xboole_0(A_11177) | ~r2_hidden(A_11178, k2_zfmisc_1(B_11179, A_11177)))), inference(negUnitSimplification, [status(thm)], [c_38, c_208117])).
% 27.04/17.09  tff(c_208457, plain, (![A_11180, B_11181]: (~v1_xboole_0(A_11180) | v1_xboole_0(k2_zfmisc_1(B_11181, A_11180)))), inference(resolution, [status(thm)], [c_4, c_208430])).
% 27.04/17.09  tff(c_207918, plain, (![C_11134, A_11135, B_11136]: (v1_xboole_0(C_11134) | ~m1_subset_1(C_11134, k1_zfmisc_1(k2_zfmisc_1(A_11135, B_11136))) | ~v1_xboole_0(A_11135))), inference(cnfTransformation, [status(thm)], [f_104])).
% 27.04/17.09  tff(c_207925, plain, (![A_32, A_11135, B_11136]: (v1_xboole_0(k1_tarski(A_32)) | ~v1_xboole_0(A_11135) | ~r2_hidden(A_32, k2_zfmisc_1(A_11135, B_11136)))), inference(resolution, [status(thm)], [c_40, c_207918])).
% 27.04/17.09  tff(c_208336, plain, (![A_11164, A_11165, B_11166]: (~v1_xboole_0(A_11164) | ~r2_hidden(A_11165, k2_zfmisc_1(A_11164, B_11166)))), inference(negUnitSimplification, [status(thm)], [c_38, c_207925])).
% 27.04/17.09  tff(c_208360, plain, (![A_11167, B_11168]: (~v1_xboole_0(A_11167) | v1_xboole_0(k2_zfmisc_1(A_11167, B_11168)))), inference(resolution, [status(thm)], [c_4, c_208336])).
% 27.04/17.09  tff(c_149011, plain, (![A_4740]: (k1_xboole_0=A_4740 | ~v1_xboole_0(A_4740))), inference(resolution, [status(thm)], [c_89090, c_148994])).
% 27.04/17.09  tff(c_208373, plain, (![A_11167, B_11168]: (k2_zfmisc_1(A_11167, B_11168)=k1_xboole_0 | ~v1_xboole_0(A_11167))), inference(resolution, [status(thm)], [c_208360, c_149011])).
% 27.04/17.09  tff(c_208459, plain, (![B_11181, A_11180, B_11168]: (k2_zfmisc_1(k2_zfmisc_1(B_11181, A_11180), B_11168)=k1_xboole_0 | ~v1_xboole_0(A_11180))), inference(resolution, [status(thm)], [c_208457, c_208373])).
% 27.04/17.09  tff(c_208474, plain, (![B_11181, A_11180, B_11168]: (k3_zfmisc_1(B_11181, A_11180, B_11168)=k1_xboole_0 | ~v1_xboole_0(A_11180))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_208459])).
% 27.04/17.09  tff(c_211377, plain, (![B_11340, A_11341, B_11342]: (k3_zfmisc_1(B_11340, A_11341, B_11342)='#skF_8' | ~v1_xboole_0(A_11341))), inference(demodulation, [status(thm), theory('equality')], [c_208479, c_208474])).
% 27.04/17.09  tff(c_211674, plain, (![B_11340, B_11342]: (k3_zfmisc_1(B_11340, '#skF_8', B_11342)='#skF_8')), inference(resolution, [status(thm)], [c_208496, c_211377])).
% 27.04/17.09  tff(c_208105, plain, (k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9')!=k1_xboole_0), inference(resolution, [status(thm)], [c_208086, c_184139])).
% 27.04/17.09  tff(c_208492, plain, (k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_208479, c_208105])).
% 27.04/17.09  tff(c_211682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211674, c_208492])).
% 27.04/17.09  tff(c_211684, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_208391])).
% 27.04/17.09  tff(c_211939, plain, (![A_11385, B_11386, C_11387, D_11388]: (k6_mcart_1(A_11385, B_11386, C_11387, D_11388)=k2_mcart_1(k1_mcart_1(D_11388)) | ~m1_subset_1(D_11388, k3_zfmisc_1(A_11385, B_11386, C_11387)) | k1_xboole_0=C_11387 | k1_xboole_0=B_11386 | k1_xboole_0=A_11385)), inference(cnfTransformation, [status(thm)], [f_139])).
% 27.04/17.09  tff(c_211942, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_207262, c_211939])).
% 27.04/17.09  tff(c_211945, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_208106, c_211684, c_208108, c_211942])).
% 27.04/17.09  tff(c_207365, plain, (![A_11103, B_11104, C_11105]: (r2_hidden(k1_mcart_1(A_11103), B_11104) | ~r2_hidden(A_11103, k2_zfmisc_1(B_11104, C_11105)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 27.04/17.09  tff(c_218073, plain, (![A_11680, A_11681, B_11682, C_11683]: (r2_hidden(k1_mcart_1(A_11680), k2_zfmisc_1(A_11681, B_11682)) | ~r2_hidden(A_11680, k3_zfmisc_1(A_11681, B_11682, C_11683)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_207365])).
% 27.04/17.09  tff(c_218119, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_184140, c_218073])).
% 27.04/17.09  tff(c_218135, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_218119, c_52])).
% 27.04/17.09  tff(c_218154, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_211945, c_218135])).
% 27.04/17.09  tff(c_218156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_207340, c_218154])).
% 27.04/17.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.04/17.09  
% 27.04/17.09  Inference rules
% 27.04/17.09  ----------------------
% 27.04/17.09  #Ref     : 44
% 27.04/17.09  #Sup     : 53775
% 27.04/17.09  #Fact    : 0
% 27.04/17.09  #Define  : 0
% 27.04/17.09  #Split   : 139
% 27.04/17.09  #Chain   : 0
% 27.04/17.09  #Close   : 0
% 27.04/17.09  
% 27.04/17.09  Ordering : KBO
% 27.04/17.09  
% 27.04/17.09  Simplification rules
% 27.04/17.09  ----------------------
% 27.04/17.09  #Subsume      : 19565
% 27.04/17.09  #Demod        : 16474
% 27.04/17.09  #Tautology    : 16729
% 27.04/17.09  #SimpNegUnit  : 1408
% 27.04/17.09  #BackRed      : 906
% 27.04/17.09  
% 27.04/17.09  #Partial instantiations: 0
% 27.04/17.09  #Strategies tried      : 1
% 27.04/17.09  
% 27.04/17.09  Timing (in seconds)
% 27.04/17.09  ----------------------
% 27.04/17.09  Preprocessing        : 0.34
% 27.04/17.09  Parsing              : 0.17
% 27.04/17.09  CNF conversion       : 0.03
% 27.04/17.09  Main loop            : 15.47
% 27.04/17.09  Inferencing          : 3.80
% 27.04/17.09  Reduction            : 5.90
% 27.04/17.09  Demodulation         : 4.09
% 27.04/17.09  BG Simplification    : 0.32
% 27.04/17.09  Subsumption          : 4.36
% 27.04/17.09  Abstraction          : 0.46
% 27.04/17.09  MUC search           : 0.00
% 27.04/17.09  Cooper               : 0.00
% 27.04/17.09  Total                : 16.28
% 27.04/17.09  Index Insertion      : 0.00
% 27.04/17.09  Index Deletion       : 0.00
% 27.04/17.09  Index Matching       : 0.00
% 27.04/17.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
