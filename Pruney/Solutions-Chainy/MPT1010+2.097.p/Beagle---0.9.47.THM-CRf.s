%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:18 EST 2020

% Result     : Theorem 9.86s
% Output     : CNFRefutation 9.86s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 949 expanded)
%              Number of leaves         :   45 ( 332 expanded)
%              Depth                    :   16
%              Number of atoms          :  167 (2675 expanded)
%              Number of equality atoms :   71 (1201 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_13 > #skF_5 > #skF_2 > #skF_8 > #skF_7 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_140,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_100,plain,(
    r2_hidden('#skF_12','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_98,plain,(
    k1_funct_1('#skF_13','#skF_12') != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_102,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_10',k1_tarski('#skF_11')))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_163,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_167,plain,(
    v5_relat_1('#skF_13',k1_tarski('#skF_11')) ),
    inference(resolution,[status(thm)],[c_102,c_163])).

tff(c_60,plain,(
    ! [A_27,B_28] : v1_relat_1(k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_154,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_157,plain,
    ( v1_relat_1('#skF_13')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_10',k1_tarski('#skF_11'))) ),
    inference(resolution,[status(thm)],[c_102,c_154])).

tff(c_160,plain,(
    v1_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_157])).

tff(c_106,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_104,plain,(
    v1_funct_2('#skF_13','#skF_10',k1_tarski('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_743,plain,(
    ! [A_1671,B_1672,C_1673] :
      ( k1_relset_1(A_1671,B_1672,C_1673) = k1_relat_1(C_1673)
      | ~ m1_subset_1(C_1673,k1_zfmisc_1(k2_zfmisc_1(A_1671,B_1672))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_749,plain,(
    k1_relset_1('#skF_10',k1_tarski('#skF_11'),'#skF_13') = k1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_102,c_743])).

tff(c_2614,plain,(
    ! [B_3565,A_3566,C_3567] :
      ( k1_xboole_0 = B_3565
      | k1_relset_1(A_3566,B_3565,C_3567) = A_3566
      | ~ v1_funct_2(C_3567,A_3566,B_3565)
      | ~ m1_subset_1(C_3567,k1_zfmisc_1(k2_zfmisc_1(A_3566,B_3565))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2619,plain,
    ( k1_tarski('#skF_11') = k1_xboole_0
    | k1_relset_1('#skF_10',k1_tarski('#skF_11'),'#skF_13') = '#skF_10'
    | ~ v1_funct_2('#skF_13','#skF_10',k1_tarski('#skF_11')) ),
    inference(resolution,[status(thm)],[c_102,c_2614])).

tff(c_2622,plain,
    ( k1_tarski('#skF_11') = k1_xboole_0
    | k1_relat_1('#skF_13') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_749,c_2619])).

tff(c_2623,plain,(
    k1_relat_1('#skF_13') = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_2622])).

tff(c_1909,plain,(
    ! [B_3065,C_3066,A_3067] :
      ( r2_hidden(k1_funct_1(B_3065,C_3066),A_3067)
      | ~ r2_hidden(C_3066,k1_relat_1(B_3065))
      | ~ v1_funct_1(B_3065)
      | ~ v5_relat_1(B_3065,A_3067)
      | ~ v1_relat_1(B_3065) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6567,plain,(
    ! [B_6811,C_6812,A_6813] :
      ( k1_funct_1(B_6811,C_6812) = A_6813
      | ~ r2_hidden(C_6812,k1_relat_1(B_6811))
      | ~ v1_funct_1(B_6811)
      | ~ v5_relat_1(B_6811,k1_tarski(A_6813))
      | ~ v1_relat_1(B_6811) ) ),
    inference(resolution,[status(thm)],[c_1909,c_20])).

tff(c_6584,plain,(
    ! [C_6812,A_6813] :
      ( k1_funct_1('#skF_13',C_6812) = A_6813
      | ~ r2_hidden(C_6812,'#skF_10')
      | ~ v1_funct_1('#skF_13')
      | ~ v5_relat_1('#skF_13',k1_tarski(A_6813))
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2623,c_6567])).

tff(c_6640,plain,(
    ! [C_6857,A_6858] :
      ( k1_funct_1('#skF_13',C_6857) = A_6858
      | ~ r2_hidden(C_6857,'#skF_10')
      | ~ v5_relat_1('#skF_13',k1_tarski(A_6858)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_106,c_6584])).

tff(c_6713,plain,(
    ! [A_6902] :
      ( k1_funct_1('#skF_13','#skF_12') = A_6902
      | ~ v5_relat_1('#skF_13',k1_tarski(A_6902)) ) ),
    inference(resolution,[status(thm)],[c_100,c_6640])).

tff(c_6720,plain,(
    k1_funct_1('#skF_13','#skF_12') = '#skF_11' ),
    inference(resolution,[status(thm)],[c_167,c_6713])).

tff(c_6724,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_6720])).

tff(c_6725,plain,(
    k1_tarski('#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2622])).

tff(c_6730,plain,(
    v1_funct_2('#skF_13','#skF_10',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6725,c_104])).

tff(c_6729,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_10',k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6725,c_102])).

tff(c_88,plain,(
    ! [C_53,A_51] :
      ( k1_xboole_0 = C_53
      | ~ v1_funct_2(C_53,A_51,k1_xboole_0)
      | k1_xboole_0 = A_51
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6920,plain,
    ( k1_xboole_0 = '#skF_13'
    | ~ v1_funct_2('#skF_13','#skF_10',k1_xboole_0)
    | k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6729,c_88])).

tff(c_6944,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6730,c_6920])).

tff(c_6954,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_6944])).

tff(c_197,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_7'(A_90,B_91),A_90)
      | k1_xboole_0 = A_90
      | k1_tarski(B_91) = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_215,plain,(
    ! [A_1,B_2,B_91] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_1,B_2),B_91),A_1)
      | k4_xboole_0(A_1,B_2) = k1_xboole_0
      | k4_xboole_0(A_1,B_2) = k1_tarski(B_91) ) ),
    inference(resolution,[status(thm)],[c_197,c_6])).

tff(c_10116,plain,(
    ! [A_10089,B_10090,B_10091] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_10089,B_10090),B_10091),A_10089)
      | k4_xboole_0(A_10089,B_10090) = '#skF_10'
      | k4_xboole_0(A_10089,B_10090) = k1_tarski(B_10091) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6954,c_215])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_216,plain,(
    ! [A_1,B_2,B_91] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_1,B_2),B_91),B_2)
      | k4_xboole_0(A_1,B_2) = k1_xboole_0
      | k4_xboole_0(A_1,B_2) = k1_tarski(B_91) ) ),
    inference(resolution,[status(thm)],[c_197,c_4])).

tff(c_9085,plain,(
    ! [A_1,B_2,B_91] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_1,B_2),B_91),B_2)
      | k4_xboole_0(A_1,B_2) = '#skF_10'
      | k4_xboole_0(A_1,B_2) = k1_tarski(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6954,c_216])).

tff(c_10218,plain,(
    ! [A_10089,B_10091] :
      ( k4_xboole_0(A_10089,A_10089) = '#skF_10'
      | k4_xboole_0(A_10089,A_10089) = k1_tarski(B_10091) ) ),
    inference(resolution,[status(thm)],[c_10116,c_9085])).

tff(c_10278,plain,(
    ! [A_10089,B_10091] :
      ( k4_xboole_0(A_10089,A_10089) = '#skF_10'
      | k1_tarski(B_10091) != '#skF_10' ) ),
    inference(factorization,[status(thm),theory(equality)],[c_10218])).

tff(c_10462,plain,(
    ! [B_10091] : k1_tarski(B_10091) != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_10278])).

tff(c_6761,plain,(
    ! [C_11] :
      ( C_11 = '#skF_11'
      | ~ r2_hidden(C_11,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6725,c_20])).

tff(c_7085,plain,(
    ! [C_7552] :
      ( C_7552 = '#skF_11'
      | ~ r2_hidden(C_7552,'#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6954,c_6761])).

tff(c_7154,plain,(
    '#skF_11' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_100,c_7085])).

tff(c_6962,plain,(
    k1_tarski('#skF_11') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6954,c_6725])).

tff(c_7227,plain,(
    k1_tarski('#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7154,c_6962])).

tff(c_10504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10462,c_7227])).

tff(c_10510,plain,(
    ! [A_10268] : k4_xboole_0(A_10268,A_10268) = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_10278])).

tff(c_10577,plain,(
    ! [D_10312,A_10313] :
      ( r2_hidden(D_10312,A_10313)
      | ~ r2_hidden(D_10312,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10510,c_6])).

tff(c_10646,plain,(
    ! [A_10313] : r2_hidden('#skF_12',A_10313) ),
    inference(resolution,[status(thm)],[c_100,c_10577])).

tff(c_10661,plain,(
    ! [A_10357] : r2_hidden('#skF_12',A_10357) ),
    inference(resolution,[status(thm)],[c_100,c_10577])).

tff(c_10712,plain,(
    ! [B_2] : ~ r2_hidden('#skF_12',B_2) ),
    inference(resolution,[status(thm)],[c_10661,c_4])).

tff(c_10745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10646,c_10712])).

tff(c_10746,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_6944])).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6764,plain,(
    r2_hidden('#skF_11',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6725,c_22])).

tff(c_10752,plain,(
    r2_hidden('#skF_11','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10746,c_6764])).

tff(c_13087,plain,(
    ! [A_12846,B_12847,B_12848] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_12846,B_12847),B_12848),A_12846)
      | k4_xboole_0(A_12846,B_12847) = '#skF_13'
      | k4_xboole_0(A_12846,B_12847) = k1_tarski(B_12848) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10746,c_215])).

tff(c_12766,plain,(
    ! [A_1,B_2,B_91] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_1,B_2),B_91),B_2)
      | k4_xboole_0(A_1,B_2) = '#skF_13'
      | k4_xboole_0(A_1,B_2) = k1_tarski(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10746,c_216])).

tff(c_13175,plain,(
    ! [A_12846,B_12848] :
      ( k4_xboole_0(A_12846,A_12846) = '#skF_13'
      | k4_xboole_0(A_12846,A_12846) = k1_tarski(B_12848) ) ),
    inference(resolution,[status(thm)],[c_13087,c_12766])).

tff(c_13193,plain,(
    ! [A_12846,B_12848] :
      ( k4_xboole_0(A_12846,A_12846) = '#skF_13'
      | k1_tarski(B_12848) != '#skF_13' ) ),
    inference(factorization,[status(thm),theory(equality)],[c_13175])).

tff(c_13351,plain,(
    ! [B_12848] : k1_tarski(B_12848) != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_13193])).

tff(c_10755,plain,(
    k1_tarski('#skF_11') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10746,c_6725])).

tff(c_13355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13351,c_10755])).

tff(c_13363,plain,(
    ! [A_12937] : k4_xboole_0(A_12937,A_12937) = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_13193])).

tff(c_13404,plain,(
    ! [D_12981,A_12982] :
      ( r2_hidden(D_12981,A_12982)
      | ~ r2_hidden(D_12981,'#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13363,c_6])).

tff(c_13455,plain,(
    ! [A_12982] : r2_hidden('#skF_11',A_12982) ),
    inference(resolution,[status(thm)],[c_10752,c_13404])).

tff(c_13468,plain,(
    ! [A_13026] : r2_hidden('#skF_11',A_13026) ),
    inference(resolution,[status(thm)],[c_10752,c_13404])).

tff(c_13519,plain,(
    ! [B_2] : ~ r2_hidden('#skF_11',B_2) ),
    inference(resolution,[status(thm)],[c_13468,c_4])).

tff(c_13550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13455,c_13519])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.86/3.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.86/3.12  
% 9.86/3.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.86/3.12  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_13 > #skF_5 > #skF_2 > #skF_8 > #skF_7 > #skF_12 > #skF_4
% 9.86/3.12  
% 9.86/3.12  %Foreground sorts:
% 9.86/3.12  
% 9.86/3.12  
% 9.86/3.12  %Background operators:
% 9.86/3.12  
% 9.86/3.12  
% 9.86/3.12  %Foreground operators:
% 9.86/3.12  tff('#skF_9', type, '#skF_9': $i > $i).
% 9.86/3.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.86/3.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.86/3.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.86/3.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.86/3.12  tff('#skF_11', type, '#skF_11': $i).
% 9.86/3.12  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.86/3.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.86/3.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.86/3.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.86/3.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.86/3.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.86/3.12  tff('#skF_10', type, '#skF_10': $i).
% 9.86/3.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.86/3.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.86/3.12  tff('#skF_13', type, '#skF_13': $i).
% 9.86/3.12  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.86/3.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.86/3.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.86/3.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.86/3.12  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.86/3.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.86/3.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.86/3.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.86/3.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.86/3.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.86/3.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.86/3.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.86/3.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.86/3.12  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 9.86/3.12  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 9.86/3.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.86/3.12  tff('#skF_12', type, '#skF_12': $i).
% 9.86/3.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.86/3.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.86/3.12  
% 9.86/3.14  tff(f_151, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 9.86/3.14  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.86/3.14  tff(f_78, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.86/3.14  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.86/3.14  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.86/3.14  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.86/3.14  tff(f_100, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 9.86/3.14  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 9.86/3.14  tff(f_69, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 9.86/3.14  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.86/3.14  tff(c_100, plain, (r2_hidden('#skF_12', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.86/3.14  tff(c_98, plain, (k1_funct_1('#skF_13', '#skF_12')!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.86/3.14  tff(c_102, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_10', k1_tarski('#skF_11'))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.86/3.14  tff(c_163, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.86/3.14  tff(c_167, plain, (v5_relat_1('#skF_13', k1_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_102, c_163])).
% 9.86/3.14  tff(c_60, plain, (![A_27, B_28]: (v1_relat_1(k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.86/3.14  tff(c_154, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.86/3.14  tff(c_157, plain, (v1_relat_1('#skF_13') | ~v1_relat_1(k2_zfmisc_1('#skF_10', k1_tarski('#skF_11')))), inference(resolution, [status(thm)], [c_102, c_154])).
% 9.86/3.14  tff(c_160, plain, (v1_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_157])).
% 9.86/3.14  tff(c_106, plain, (v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.86/3.14  tff(c_104, plain, (v1_funct_2('#skF_13', '#skF_10', k1_tarski('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 9.86/3.14  tff(c_743, plain, (![A_1671, B_1672, C_1673]: (k1_relset_1(A_1671, B_1672, C_1673)=k1_relat_1(C_1673) | ~m1_subset_1(C_1673, k1_zfmisc_1(k2_zfmisc_1(A_1671, B_1672))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 9.86/3.14  tff(c_749, plain, (k1_relset_1('#skF_10', k1_tarski('#skF_11'), '#skF_13')=k1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_102, c_743])).
% 9.86/3.14  tff(c_2614, plain, (![B_3565, A_3566, C_3567]: (k1_xboole_0=B_3565 | k1_relset_1(A_3566, B_3565, C_3567)=A_3566 | ~v1_funct_2(C_3567, A_3566, B_3565) | ~m1_subset_1(C_3567, k1_zfmisc_1(k2_zfmisc_1(A_3566, B_3565))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.86/3.14  tff(c_2619, plain, (k1_tarski('#skF_11')=k1_xboole_0 | k1_relset_1('#skF_10', k1_tarski('#skF_11'), '#skF_13')='#skF_10' | ~v1_funct_2('#skF_13', '#skF_10', k1_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_102, c_2614])).
% 9.86/3.14  tff(c_2622, plain, (k1_tarski('#skF_11')=k1_xboole_0 | k1_relat_1('#skF_13')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_749, c_2619])).
% 9.86/3.14  tff(c_2623, plain, (k1_relat_1('#skF_13')='#skF_10'), inference(splitLeft, [status(thm)], [c_2622])).
% 9.86/3.14  tff(c_1909, plain, (![B_3065, C_3066, A_3067]: (r2_hidden(k1_funct_1(B_3065, C_3066), A_3067) | ~r2_hidden(C_3066, k1_relat_1(B_3065)) | ~v1_funct_1(B_3065) | ~v5_relat_1(B_3065, A_3067) | ~v1_relat_1(B_3065))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.86/3.14  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.86/3.14  tff(c_6567, plain, (![B_6811, C_6812, A_6813]: (k1_funct_1(B_6811, C_6812)=A_6813 | ~r2_hidden(C_6812, k1_relat_1(B_6811)) | ~v1_funct_1(B_6811) | ~v5_relat_1(B_6811, k1_tarski(A_6813)) | ~v1_relat_1(B_6811))), inference(resolution, [status(thm)], [c_1909, c_20])).
% 9.86/3.14  tff(c_6584, plain, (![C_6812, A_6813]: (k1_funct_1('#skF_13', C_6812)=A_6813 | ~r2_hidden(C_6812, '#skF_10') | ~v1_funct_1('#skF_13') | ~v5_relat_1('#skF_13', k1_tarski(A_6813)) | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_2623, c_6567])).
% 9.86/3.14  tff(c_6640, plain, (![C_6857, A_6858]: (k1_funct_1('#skF_13', C_6857)=A_6858 | ~r2_hidden(C_6857, '#skF_10') | ~v5_relat_1('#skF_13', k1_tarski(A_6858)))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_106, c_6584])).
% 9.86/3.14  tff(c_6713, plain, (![A_6902]: (k1_funct_1('#skF_13', '#skF_12')=A_6902 | ~v5_relat_1('#skF_13', k1_tarski(A_6902)))), inference(resolution, [status(thm)], [c_100, c_6640])).
% 9.86/3.14  tff(c_6720, plain, (k1_funct_1('#skF_13', '#skF_12')='#skF_11'), inference(resolution, [status(thm)], [c_167, c_6713])).
% 9.86/3.14  tff(c_6724, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_6720])).
% 9.86/3.14  tff(c_6725, plain, (k1_tarski('#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_2622])).
% 9.86/3.14  tff(c_6730, plain, (v1_funct_2('#skF_13', '#skF_10', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6725, c_104])).
% 9.86/3.14  tff(c_6729, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_10', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6725, c_102])).
% 9.86/3.14  tff(c_88, plain, (![C_53, A_51]: (k1_xboole_0=C_53 | ~v1_funct_2(C_53, A_51, k1_xboole_0) | k1_xboole_0=A_51 | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 9.86/3.14  tff(c_6920, plain, (k1_xboole_0='#skF_13' | ~v1_funct_2('#skF_13', '#skF_10', k1_xboole_0) | k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_6729, c_88])).
% 9.86/3.14  tff(c_6944, plain, (k1_xboole_0='#skF_13' | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_6730, c_6920])).
% 9.86/3.14  tff(c_6954, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_6944])).
% 9.86/3.14  tff(c_197, plain, (![A_90, B_91]: (r2_hidden('#skF_7'(A_90, B_91), A_90) | k1_xboole_0=A_90 | k1_tarski(B_91)=A_90)), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.86/3.14  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.86/3.14  tff(c_215, plain, (![A_1, B_2, B_91]: (r2_hidden('#skF_7'(k4_xboole_0(A_1, B_2), B_91), A_1) | k4_xboole_0(A_1, B_2)=k1_xboole_0 | k4_xboole_0(A_1, B_2)=k1_tarski(B_91))), inference(resolution, [status(thm)], [c_197, c_6])).
% 9.86/3.14  tff(c_10116, plain, (![A_10089, B_10090, B_10091]: (r2_hidden('#skF_7'(k4_xboole_0(A_10089, B_10090), B_10091), A_10089) | k4_xboole_0(A_10089, B_10090)='#skF_10' | k4_xboole_0(A_10089, B_10090)=k1_tarski(B_10091))), inference(demodulation, [status(thm), theory('equality')], [c_6954, c_215])).
% 9.86/3.14  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.86/3.14  tff(c_216, plain, (![A_1, B_2, B_91]: (~r2_hidden('#skF_7'(k4_xboole_0(A_1, B_2), B_91), B_2) | k4_xboole_0(A_1, B_2)=k1_xboole_0 | k4_xboole_0(A_1, B_2)=k1_tarski(B_91))), inference(resolution, [status(thm)], [c_197, c_4])).
% 9.86/3.14  tff(c_9085, plain, (![A_1, B_2, B_91]: (~r2_hidden('#skF_7'(k4_xboole_0(A_1, B_2), B_91), B_2) | k4_xboole_0(A_1, B_2)='#skF_10' | k4_xboole_0(A_1, B_2)=k1_tarski(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_6954, c_216])).
% 9.86/3.14  tff(c_10218, plain, (![A_10089, B_10091]: (k4_xboole_0(A_10089, A_10089)='#skF_10' | k4_xboole_0(A_10089, A_10089)=k1_tarski(B_10091))), inference(resolution, [status(thm)], [c_10116, c_9085])).
% 9.86/3.14  tff(c_10278, plain, (![A_10089, B_10091]: (k4_xboole_0(A_10089, A_10089)='#skF_10' | k1_tarski(B_10091)!='#skF_10')), inference(factorization, [status(thm), theory('equality')], [c_10218])).
% 9.86/3.14  tff(c_10462, plain, (![B_10091]: (k1_tarski(B_10091)!='#skF_10')), inference(splitLeft, [status(thm)], [c_10278])).
% 9.86/3.14  tff(c_6761, plain, (![C_11]: (C_11='#skF_11' | ~r2_hidden(C_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6725, c_20])).
% 9.86/3.14  tff(c_7085, plain, (![C_7552]: (C_7552='#skF_11' | ~r2_hidden(C_7552, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_6954, c_6761])).
% 9.86/3.14  tff(c_7154, plain, ('#skF_11'='#skF_12'), inference(resolution, [status(thm)], [c_100, c_7085])).
% 9.86/3.14  tff(c_6962, plain, (k1_tarski('#skF_11')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_6954, c_6725])).
% 9.86/3.14  tff(c_7227, plain, (k1_tarski('#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_7154, c_6962])).
% 9.86/3.14  tff(c_10504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10462, c_7227])).
% 9.86/3.14  tff(c_10510, plain, (![A_10268]: (k4_xboole_0(A_10268, A_10268)='#skF_10')), inference(splitRight, [status(thm)], [c_10278])).
% 9.86/3.14  tff(c_10577, plain, (![D_10312, A_10313]: (r2_hidden(D_10312, A_10313) | ~r2_hidden(D_10312, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_10510, c_6])).
% 9.86/3.14  tff(c_10646, plain, (![A_10313]: (r2_hidden('#skF_12', A_10313))), inference(resolution, [status(thm)], [c_100, c_10577])).
% 9.86/3.14  tff(c_10661, plain, (![A_10357]: (r2_hidden('#skF_12', A_10357))), inference(resolution, [status(thm)], [c_100, c_10577])).
% 9.86/3.14  tff(c_10712, plain, (![B_2]: (~r2_hidden('#skF_12', B_2))), inference(resolution, [status(thm)], [c_10661, c_4])).
% 9.86/3.14  tff(c_10745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10646, c_10712])).
% 9.86/3.14  tff(c_10746, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_6944])).
% 9.86/3.14  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.86/3.14  tff(c_6764, plain, (r2_hidden('#skF_11', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6725, c_22])).
% 9.86/3.14  tff(c_10752, plain, (r2_hidden('#skF_11', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_10746, c_6764])).
% 9.86/3.14  tff(c_13087, plain, (![A_12846, B_12847, B_12848]: (r2_hidden('#skF_7'(k4_xboole_0(A_12846, B_12847), B_12848), A_12846) | k4_xboole_0(A_12846, B_12847)='#skF_13' | k4_xboole_0(A_12846, B_12847)=k1_tarski(B_12848))), inference(demodulation, [status(thm), theory('equality')], [c_10746, c_215])).
% 9.86/3.14  tff(c_12766, plain, (![A_1, B_2, B_91]: (~r2_hidden('#skF_7'(k4_xboole_0(A_1, B_2), B_91), B_2) | k4_xboole_0(A_1, B_2)='#skF_13' | k4_xboole_0(A_1, B_2)=k1_tarski(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_10746, c_216])).
% 9.86/3.14  tff(c_13175, plain, (![A_12846, B_12848]: (k4_xboole_0(A_12846, A_12846)='#skF_13' | k4_xboole_0(A_12846, A_12846)=k1_tarski(B_12848))), inference(resolution, [status(thm)], [c_13087, c_12766])).
% 9.86/3.14  tff(c_13193, plain, (![A_12846, B_12848]: (k4_xboole_0(A_12846, A_12846)='#skF_13' | k1_tarski(B_12848)!='#skF_13')), inference(factorization, [status(thm), theory('equality')], [c_13175])).
% 9.86/3.14  tff(c_13351, plain, (![B_12848]: (k1_tarski(B_12848)!='#skF_13')), inference(splitLeft, [status(thm)], [c_13193])).
% 9.86/3.14  tff(c_10755, plain, (k1_tarski('#skF_11')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_10746, c_6725])).
% 9.86/3.14  tff(c_13355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13351, c_10755])).
% 9.86/3.14  tff(c_13363, plain, (![A_12937]: (k4_xboole_0(A_12937, A_12937)='#skF_13')), inference(splitRight, [status(thm)], [c_13193])).
% 9.86/3.14  tff(c_13404, plain, (![D_12981, A_12982]: (r2_hidden(D_12981, A_12982) | ~r2_hidden(D_12981, '#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_13363, c_6])).
% 9.86/3.14  tff(c_13455, plain, (![A_12982]: (r2_hidden('#skF_11', A_12982))), inference(resolution, [status(thm)], [c_10752, c_13404])).
% 9.86/3.14  tff(c_13468, plain, (![A_13026]: (r2_hidden('#skF_11', A_13026))), inference(resolution, [status(thm)], [c_10752, c_13404])).
% 9.86/3.14  tff(c_13519, plain, (![B_2]: (~r2_hidden('#skF_11', B_2))), inference(resolution, [status(thm)], [c_13468, c_4])).
% 9.86/3.14  tff(c_13550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13455, c_13519])).
% 9.86/3.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.86/3.14  
% 9.86/3.14  Inference rules
% 9.86/3.14  ----------------------
% 9.86/3.14  #Ref     : 0
% 9.86/3.14  #Sup     : 2420
% 9.86/3.14  #Fact    : 4
% 9.86/3.14  #Define  : 0
% 9.86/3.14  #Split   : 19
% 9.86/3.14  #Chain   : 0
% 9.86/3.14  #Close   : 0
% 9.86/3.14  
% 9.86/3.14  Ordering : KBO
% 9.86/3.14  
% 9.86/3.14  Simplification rules
% 9.86/3.14  ----------------------
% 9.86/3.14  #Subsume      : 439
% 9.86/3.14  #Demod        : 806
% 9.86/3.14  #Tautology    : 517
% 9.86/3.14  #SimpNegUnit  : 61
% 9.86/3.14  #BackRed      : 102
% 9.86/3.14  
% 9.86/3.14  #Partial instantiations: 7250
% 9.86/3.14  #Strategies tried      : 1
% 9.86/3.14  
% 9.86/3.14  Timing (in seconds)
% 9.86/3.14  ----------------------
% 9.86/3.14  Preprocessing        : 0.36
% 9.86/3.14  Parsing              : 0.18
% 9.86/3.15  CNF conversion       : 0.03
% 9.86/3.15  Main loop            : 2.00
% 9.86/3.15  Inferencing          : 0.77
% 9.86/3.15  Reduction            : 0.54
% 9.86/3.15  Demodulation         : 0.38
% 9.86/3.15  BG Simplification    : 0.10
% 9.86/3.15  Subsumption          : 0.42
% 9.86/3.15  Abstraction          : 0.10
% 9.86/3.15  MUC search           : 0.00
% 9.86/3.15  Cooper               : 0.00
% 9.86/3.15  Total                : 2.41
% 9.86/3.15  Index Insertion      : 0.00
% 9.86/3.15  Index Deletion       : 0.00
% 9.86/3.15  Index Matching       : 0.00
% 9.86/3.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
