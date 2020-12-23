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
% DateTime   : Thu Dec  3 10:10:10 EST 2020

% Result     : Theorem 10.49s
% Output     : CNFRefutation 11.42s
% Verified   : 
% Statistics : Number of formulae       : 1012 (7060 expanded)
%              Number of leaves         :   40 (2187 expanded)
%              Depth                    :   22
%              Number of atoms          : 1738 (18165 expanded)
%              Number of equality atoms :  553 (4426 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_128,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_108,axiom,(
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

tff(c_24,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20408,plain,(
    ! [C_2293,B_2294,A_2295] :
      ( r2_hidden(C_2293,B_2294)
      | ~ r2_hidden(C_2293,A_2295)
      | ~ r1_tarski(A_2295,B_2294) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20478,plain,(
    ! [A_2303,B_2304] :
      ( r2_hidden('#skF_1'(A_2303),B_2304)
      | ~ r1_tarski(A_2303,B_2304)
      | v1_xboole_0(A_2303) ) ),
    inference(resolution,[status(thm)],[c_4,c_20408])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20499,plain,(
    ! [B_2305,A_2306] :
      ( ~ v1_xboole_0(B_2305)
      | ~ r1_tarski(A_2306,B_2305)
      | v1_xboole_0(A_2306) ) ),
    inference(resolution,[status(thm)],[c_20478,c_2])).

tff(c_20520,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_20499])).

tff(c_20521,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_20520])).

tff(c_20524,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_20521,c_4])).

tff(c_20429,plain,(
    ! [A_1,B_2294] :
      ( r2_hidden('#skF_1'(A_1),B_2294)
      | ~ r1_tarski(A_1,B_2294)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_20408])).

tff(c_20544,plain,(
    ! [A_2311,B_2312] :
      ( r2_hidden('#skF_1'(A_2311),B_2312)
      | ~ r1_tarski(A_2311,B_2312) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20521,c_20429])).

tff(c_28,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20377,plain,(
    ! [A_2287,B_2288,C_2289] :
      ( ~ r1_xboole_0(A_2287,B_2288)
      | ~ r2_hidden(C_2289,B_2288)
      | ~ r2_hidden(C_2289,A_2287) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20386,plain,(
    ! [C_2289,B_22,A_21] :
      ( ~ r2_hidden(C_2289,B_22)
      | ~ r2_hidden(C_2289,k4_xboole_0(A_21,B_22)) ) ),
    inference(resolution,[status(thm)],[c_28,c_20377])).

tff(c_20643,plain,(
    ! [A_2323,B_2324,A_2325] :
      ( ~ r2_hidden('#skF_1'(A_2323),B_2324)
      | ~ r1_tarski(A_2323,k4_xboole_0(A_2325,B_2324)) ) ),
    inference(resolution,[status(thm)],[c_20544,c_20386])).

tff(c_20655,plain,(
    ! [A_2329,A_2330] : ~ r1_tarski(A_2329,k4_xboole_0(A_2330,A_2329)) ),
    inference(resolution,[status(thm)],[c_20524,c_20643])).

tff(c_20660,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_24,c_20655])).

tff(c_20661,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_20520])).

tff(c_17375,plain,(
    ! [C_1958,B_1959,A_1960] :
      ( r2_hidden(C_1958,B_1959)
      | ~ r2_hidden(C_1958,A_1960)
      | ~ r1_tarski(A_1960,B_1959) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_17475,plain,(
    ! [A_1974,B_1975] :
      ( r2_hidden('#skF_1'(A_1974),B_1975)
      | ~ r1_tarski(A_1974,B_1975)
      | v1_xboole_0(A_1974) ) ),
    inference(resolution,[status(thm)],[c_4,c_17375])).

tff(c_17496,plain,(
    ! [B_1976,A_1977] :
      ( ~ v1_xboole_0(B_1976)
      | ~ r1_tarski(A_1977,B_1976)
      | v1_xboole_0(A_1977) ) ),
    inference(resolution,[status(thm)],[c_17475,c_2])).

tff(c_17508,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_17496])).

tff(c_17509,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_17508])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ r1_xboole_0(A_18,B_19)
      | ~ r1_tarski(C_20,B_19)
      | ~ r1_tarski(C_20,A_18)
      | v1_xboole_0(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_17637,plain,(
    ! [A_1997,B_1998,C_1999] :
      ( ~ r1_xboole_0(A_1997,B_1998)
      | ~ r1_tarski(C_1999,B_1998)
      | ~ r1_tarski(C_1999,A_1997) ) ),
    inference(negUnitSimplification,[status(thm)],[c_17509,c_26])).

tff(c_17641,plain,(
    ! [C_2000,B_2001,A_2002] :
      ( ~ r1_tarski(C_2000,B_2001)
      | ~ r1_tarski(C_2000,k4_xboole_0(A_2002,B_2001)) ) ),
    inference(resolution,[status(thm)],[c_28,c_17637])).

tff(c_17649,plain,(
    ! [B_2001] : ~ r1_tarski(k1_xboole_0,B_2001) ),
    inference(resolution,[status(thm)],[c_24,c_17641])).

tff(c_17654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_17649])).

tff(c_17655,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_17508])).

tff(c_22,plain,(
    ! [B_16] : r1_tarski(B_16,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_15631,plain,(
    ! [C_1787,B_1788,A_1789] :
      ( r2_hidden(C_1787,B_1788)
      | ~ r2_hidden(C_1787,A_1789)
      | ~ r1_tarski(A_1789,B_1788) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15741,plain,(
    ! [A_1806,B_1807] :
      ( r2_hidden('#skF_1'(A_1806),B_1807)
      | ~ r1_tarski(A_1806,B_1807)
      | v1_xboole_0(A_1806) ) ),
    inference(resolution,[status(thm)],[c_4,c_15631])).

tff(c_15762,plain,(
    ! [B_1808,A_1809] :
      ( ~ v1_xboole_0(B_1808)
      | ~ r1_tarski(A_1809,B_1808)
      | v1_xboole_0(A_1809) ) ),
    inference(resolution,[status(thm)],[c_15741,c_2])).

tff(c_15779,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_15762])).

tff(c_15780,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_15779])).

tff(c_15847,plain,(
    ! [A_1817,B_1818,C_1819] :
      ( ~ r1_xboole_0(A_1817,B_1818)
      | ~ r1_tarski(C_1819,B_1818)
      | ~ r1_tarski(C_1819,A_1817) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15780,c_26])).

tff(c_15902,plain,(
    ! [C_1829,B_1830,A_1831] :
      ( ~ r1_tarski(C_1829,B_1830)
      | ~ r1_tarski(C_1829,k4_xboole_0(A_1831,B_1830)) ) ),
    inference(resolution,[status(thm)],[c_28,c_15847])).

tff(c_15910,plain,(
    ! [B_1830] : ~ r1_tarski(k1_xboole_0,B_1830) ),
    inference(resolution,[status(thm)],[c_24,c_15902])).

tff(c_15915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_15910])).

tff(c_15916,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_15779])).

tff(c_48,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    ! [A_25,B_26,C_27] : k2_zfmisc_1(k2_zfmisc_1(A_25,B_26),C_27) = k3_zfmisc_1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_15650,plain,(
    ! [A_1790,C_1791,B_1792] :
      ( r2_hidden(k2_mcart_1(A_1790),C_1791)
      | ~ r2_hidden(A_1790,k2_zfmisc_1(B_1792,C_1791)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_15925,plain,(
    ! [A_1832,C_1833,A_1834,B_1835] :
      ( r2_hidden(k2_mcart_1(A_1832),C_1833)
      | ~ r2_hidden(A_1832,k3_zfmisc_1(A_1834,B_1835,C_1833)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_15650])).

tff(c_15947,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_15925])).

tff(c_14185,plain,(
    ! [A_1580,B_1581] :
      ( r2_hidden('#skF_2'(A_1580,B_1581),A_1580)
      | r1_tarski(A_1580,B_1581) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14195,plain,(
    ! [A_1580,B_1581] :
      ( ~ v1_xboole_0(A_1580)
      | r1_tarski(A_1580,B_1581) ) ),
    inference(resolution,[status(thm)],[c_14185,c_2])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_72,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_88,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_72])).

tff(c_10383,plain,(
    ! [B_1106,A_1107] :
      ( B_1106 = A_1107
      | ~ r1_tarski(B_1106,A_1107)
      | ~ r1_tarski(A_1107,B_1106) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10394,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_10383])).

tff(c_15585,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_10394])).

tff(c_15589,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_14195,c_15585])).

tff(c_14265,plain,(
    ! [C_1593,B_1594,A_1595] :
      ( r2_hidden(C_1593,B_1594)
      | ~ r2_hidden(C_1593,A_1595)
      | ~ r1_tarski(A_1595,B_1594) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14380,plain,(
    ! [A_1612,B_1613] :
      ( r2_hidden('#skF_1'(A_1612),B_1613)
      | ~ r1_tarski(A_1612,B_1613)
      | v1_xboole_0(A_1612) ) ),
    inference(resolution,[status(thm)],[c_4,c_14265])).

tff(c_14401,plain,(
    ! [B_1614,A_1615] :
      ( ~ v1_xboole_0(B_1614)
      | ~ r1_tarski(A_1615,B_1614)
      | v1_xboole_0(A_1615) ) ),
    inference(resolution,[status(thm)],[c_14380,c_2])).

tff(c_14422,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_14401])).

tff(c_14423,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_14422])).

tff(c_14426,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_14423,c_4])).

tff(c_14283,plain,(
    ! [A_1,B_1594] :
      ( r2_hidden('#skF_1'(A_1),B_1594)
      | ~ r1_tarski(A_1,B_1594)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_14265])).

tff(c_14446,plain,(
    ! [A_1620,B_1621] :
      ( r2_hidden('#skF_1'(A_1620),B_1621)
      | ~ r1_tarski(A_1620,B_1621) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14423,c_14283])).

tff(c_14299,plain,(
    ! [A_1599,B_1600,C_1601] :
      ( ~ r1_xboole_0(A_1599,B_1600)
      | ~ r2_hidden(C_1601,B_1600)
      | ~ r2_hidden(C_1601,A_1599) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14308,plain,(
    ! [C_1601,B_22,A_21] :
      ( ~ r2_hidden(C_1601,B_22)
      | ~ r2_hidden(C_1601,k4_xboole_0(A_21,B_22)) ) ),
    inference(resolution,[status(thm)],[c_28,c_14299])).

tff(c_14545,plain,(
    ! [A_1632,B_1633,A_1634] :
      ( ~ r2_hidden('#skF_1'(A_1632),B_1633)
      | ~ r1_tarski(A_1632,k4_xboole_0(A_1634,B_1633)) ) ),
    inference(resolution,[status(thm)],[c_14446,c_14308])).

tff(c_14557,plain,(
    ! [A_1638,A_1639] : ~ r1_tarski(A_1638,k4_xboole_0(A_1639,A_1638)) ),
    inference(resolution,[status(thm)],[c_14426,c_14545])).

tff(c_14562,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_24,c_14557])).

tff(c_14563,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_14422])).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_87,plain,(
    r1_tarski('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_72])).

tff(c_10395,plain,
    ( '#skF_5' = '#skF_8'
    | ~ r1_tarski('#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_87,c_10383])).

tff(c_14222,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_10395])).

tff(c_14226,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_14195,c_14222])).

tff(c_14361,plain,(
    ! [A_1609,C_1610,B_1611] :
      ( r2_hidden(k2_mcart_1(A_1609),C_1610)
      | ~ r2_hidden(A_1609,k2_zfmisc_1(B_1611,C_1610)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14572,plain,(
    ! [A_1640,C_1641,A_1642,B_1643] :
      ( r2_hidden(k2_mcart_1(A_1640),C_1641)
      | ~ r2_hidden(A_1640,k3_zfmisc_1(A_1642,B_1643,C_1641)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_14361])).

tff(c_14594,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_14572])).

tff(c_14233,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_10394])).

tff(c_14237,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_14195,c_14233])).

tff(c_10416,plain,(
    ! [A_1109,B_1110] :
      ( r2_hidden('#skF_2'(A_1109,B_1110),A_1109)
      | r1_tarski(A_1109,B_1110) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10427,plain,(
    ! [A_1111,B_1112] :
      ( ~ v1_xboole_0(A_1111)
      | r1_tarski(A_1111,B_1112) ) ),
    inference(resolution,[status(thm)],[c_10416,c_2])).

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_86,plain,(
    r1_tarski('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_72])).

tff(c_10396,plain,
    ( '#skF_6' = '#skF_9'
    | ~ r1_tarski('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_10383])).

tff(c_10415,plain,(
    ~ r1_tarski('#skF_6','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_10396])).

tff(c_10437,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_10427,c_10415])).

tff(c_11708,plain,(
    ! [C_1302,B_1303,A_1304] :
      ( r2_hidden(C_1302,B_1303)
      | ~ r2_hidden(C_1302,A_1304)
      | ~ r1_tarski(A_1304,B_1303) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11860,plain,(
    ! [A_1328,B_1329] :
      ( r2_hidden('#skF_1'(A_1328),B_1329)
      | ~ r1_tarski(A_1328,B_1329)
      | v1_xboole_0(A_1328) ) ),
    inference(resolution,[status(thm)],[c_4,c_11708])).

tff(c_11881,plain,(
    ! [B_1330,A_1331] :
      ( ~ v1_xboole_0(B_1330)
      | ~ r1_tarski(A_1331,B_1330)
      | v1_xboole_0(A_1331) ) ),
    inference(resolution,[status(thm)],[c_11860,c_2])).

tff(c_11902,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_11881])).

tff(c_11924,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_11902])).

tff(c_11948,plain,(
    ! [A_1337,B_1338,C_1339] :
      ( ~ r1_xboole_0(A_1337,B_1338)
      | ~ r1_tarski(C_1339,B_1338)
      | ~ r1_tarski(C_1339,A_1337) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11924,c_26])).

tff(c_12025,plain,(
    ! [C_1351,B_1352,A_1353] :
      ( ~ r1_tarski(C_1351,B_1352)
      | ~ r1_tarski(C_1351,k4_xboole_0(A_1353,B_1352)) ) ),
    inference(resolution,[status(thm)],[c_28,c_11948])).

tff(c_12033,plain,(
    ! [B_1352] : ~ r1_tarski(k1_xboole_0,B_1352) ),
    inference(resolution,[status(thm)],[c_24,c_12025])).

tff(c_12038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_12033])).

tff(c_12039,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11902])).

tff(c_11800,plain,(
    ! [A_1316,C_1317,B_1318] :
      ( r2_hidden(k2_mcart_1(A_1316),C_1317)
      | ~ r2_hidden(A_1316,k2_zfmisc_1(B_1318,C_1317)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12102,plain,(
    ! [A_1364,C_1365,A_1366,B_1367] :
      ( r2_hidden(k2_mcart_1(A_1364),C_1365)
      | ~ r2_hidden(A_1364,k3_zfmisc_1(A_1366,B_1367,C_1365)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_11800])).

tff(c_12128,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_12102])).

tff(c_10426,plain,(
    ! [A_1109,B_1110] :
      ( ~ v1_xboole_0(A_1109)
      | r1_tarski(A_1109,B_1110) ) ),
    inference(resolution,[status(thm)],[c_10416,c_2])).

tff(c_11703,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_10394])).

tff(c_11707,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_10426,c_11703])).

tff(c_10440,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_10395])).

tff(c_10444,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_10426,c_10440])).

tff(c_10568,plain,(
    ! [C_1137,B_1138,A_1139] :
      ( r2_hidden(C_1137,B_1138)
      | ~ r2_hidden(C_1137,A_1139)
      | ~ r1_tarski(A_1139,B_1138) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10599,plain,(
    ! [A_1141,B_1142] :
      ( r2_hidden('#skF_1'(A_1141),B_1142)
      | ~ r1_tarski(A_1141,B_1142)
      | v1_xboole_0(A_1141) ) ),
    inference(resolution,[status(thm)],[c_4,c_10568])).

tff(c_10620,plain,(
    ! [B_1143,A_1144] :
      ( ~ v1_xboole_0(B_1143)
      | ~ r1_tarski(A_1144,B_1143)
      | v1_xboole_0(A_1144) ) ),
    inference(resolution,[status(thm)],[c_10599,c_2])).

tff(c_10645,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_10620])).

tff(c_10667,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_10645])).

tff(c_10691,plain,(
    ! [A_1150,B_1151,C_1152] :
      ( ~ r1_xboole_0(A_1150,B_1151)
      | ~ r1_tarski(C_1152,B_1151)
      | ~ r1_tarski(C_1152,A_1150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10667,c_26])).

tff(c_10768,plain,(
    ! [C_1164,B_1165,A_1166] :
      ( ~ r1_tarski(C_1164,B_1165)
      | ~ r1_tarski(C_1164,k4_xboole_0(A_1166,B_1165)) ) ),
    inference(resolution,[status(thm)],[c_28,c_10691])).

tff(c_10776,plain,(
    ! [B_1165] : ~ r1_tarski(k1_xboole_0,B_1165) ),
    inference(resolution,[status(thm)],[c_24,c_10768])).

tff(c_10781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_10776])).

tff(c_10782,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_10645])).

tff(c_10549,plain,(
    ! [A_1134,C_1135,B_1136] :
      ( r2_hidden(k2_mcart_1(A_1134),C_1135)
      | ~ r2_hidden(A_1134,k2_zfmisc_1(B_1136,C_1135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10857,plain,(
    ! [A_1181,C_1182,A_1183,B_1184] :
      ( r2_hidden(k2_mcart_1(A_1181),C_1182)
      | ~ r2_hidden(A_1181,k3_zfmisc_1(A_1183,B_1184,C_1182)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10549])).

tff(c_10883,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_10857])).

tff(c_10446,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_10394])).

tff(c_10450,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_10426,c_10446])).

tff(c_50,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_10892,plain,(
    ! [A_1185,B_1186,C_1187,D_1188] :
      ( k7_mcart_1(A_1185,B_1186,C_1187,D_1188) = k2_mcart_1(D_1188)
      | ~ m1_subset_1(D_1188,k3_zfmisc_1(A_1185,B_1186,C_1187))
      | k1_xboole_0 = C_1187
      | k1_xboole_0 = B_1186
      | k1_xboole_0 = A_1185 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10896,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_10892])).

tff(c_10944,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10896])).

tff(c_10946,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10944,c_10782])).

tff(c_10951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10450,c_10946])).

tff(c_10952,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_10896])).

tff(c_11081,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_10952])).

tff(c_7400,plain,(
    ! [C_795,B_796,A_797] :
      ( r2_hidden(C_795,B_796)
      | ~ r2_hidden(C_795,A_797)
      | ~ r1_tarski(A_797,B_796) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7513,plain,(
    ! [A_814,B_815] :
      ( r2_hidden('#skF_1'(A_814),B_815)
      | ~ r1_tarski(A_814,B_815)
      | v1_xboole_0(A_814) ) ),
    inference(resolution,[status(thm)],[c_4,c_7400])).

tff(c_7534,plain,(
    ! [B_816,A_817] :
      ( ~ v1_xboole_0(B_816)
      | ~ r1_tarski(A_817,B_816)
      | v1_xboole_0(A_817) ) ),
    inference(resolution,[status(thm)],[c_7513,c_2])).

tff(c_7550,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_7534])).

tff(c_7561,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_7550])).

tff(c_7655,plain,(
    ! [A_837,B_838,C_839] :
      ( ~ r1_xboole_0(A_837,B_838)
      | ~ r1_tarski(C_839,B_838)
      | ~ r1_tarski(C_839,A_837) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7561,c_26])).

tff(c_7659,plain,(
    ! [C_840,B_841,A_842] :
      ( ~ r1_tarski(C_840,B_841)
      | ~ r1_tarski(C_840,k4_xboole_0(A_842,B_841)) ) ),
    inference(resolution,[status(thm)],[c_28,c_7655])).

tff(c_7667,plain,(
    ! [B_841] : ~ r1_tarski(k1_xboole_0,B_841) ),
    inference(resolution,[status(thm)],[c_24,c_7659])).

tff(c_7672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_7667])).

tff(c_7673,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7550])).

tff(c_167,plain,(
    ! [C_76,B_77,A_78] :
      ( r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_310,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_1'(A_99),B_100)
      | ~ r1_tarski(A_99,B_100)
      | v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_4,c_167])).

tff(c_331,plain,(
    ! [B_101,A_102] :
      ( ~ v1_xboole_0(B_101)
      | ~ r1_tarski(A_102,B_101)
      | v1_xboole_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_310,c_2])).

tff(c_355,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_331])).

tff(c_356,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_413,plain,(
    ! [A_114,B_115,C_116] :
      ( ~ r1_xboole_0(A_114,B_115)
      | ~ r1_tarski(C_116,B_115)
      | ~ r1_tarski(C_116,A_114) ) ),
    inference(negUnitSimplification,[status(thm)],[c_356,c_26])).

tff(c_464,plain,(
    ! [C_125,B_126,A_127] :
      ( ~ r1_tarski(C_125,B_126)
      | ~ r1_tarski(C_125,k4_xboole_0(A_127,B_126)) ) ),
    inference(resolution,[status(thm)],[c_28,c_413])).

tff(c_472,plain,(
    ! [B_126] : ~ r1_tarski(k1_xboole_0,B_126) ),
    inference(resolution,[status(thm)],[c_24,c_464])).

tff(c_477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_472])).

tff(c_478,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_46,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9')
    | ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8')
    | ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_96,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_97,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_2'(A_64,B_65),A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    ! [A_64,B_65] :
      ( ~ v1_xboole_0(A_64)
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_97,c_2])).

tff(c_109,plain,(
    ! [B_68,A_69] :
      ( B_68 = A_69
      | ~ r1_tarski(B_68,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_124,plain,
    ( '#skF_5' = '#skF_8'
    | ~ r1_tarski('#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_87,c_109])).

tff(c_156,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_161,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_107,c_156])).

tff(c_123,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_109])).

tff(c_166,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_186,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_166])).

tff(c_622,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( k7_mcart_1(A_151,B_152,C_153,D_154) = k2_mcart_1(D_154)
      | ~ m1_subset_1(D_154,k3_zfmisc_1(A_151,B_152,C_153))
      | k1_xboole_0 = C_153
      | k1_xboole_0 = B_152
      | k1_xboole_0 = A_151 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_626,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_622])).

tff(c_663,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_626])).

tff(c_665,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_478])).

tff(c_670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_665])).

tff(c_672,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_626])).

tff(c_757,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( k6_mcart_1(A_168,B_169,C_170,D_171) = k2_mcart_1(k1_mcart_1(D_171))
      | ~ m1_subset_1(D_171,k3_zfmisc_1(A_168,B_169,C_170))
      | k1_xboole_0 = C_170
      | k1_xboole_0 = B_169
      | k1_xboole_0 = A_168 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_760,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_757])).

tff(c_763,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_672,c_760])).

tff(c_779,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_785,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_478])).

tff(c_790,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_785])).

tff(c_792,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_679,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k5_mcart_1(A_158,B_159,C_160,D_161) = k1_mcart_1(k1_mcart_1(D_161))
      | ~ m1_subset_1(D_161,k3_zfmisc_1(A_158,B_159,C_160))
      | k1_xboole_0 = C_160
      | k1_xboole_0 = B_159
      | k1_xboole_0 = A_158 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_682,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_679])).

tff(c_685,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_672,c_682])).

tff(c_883,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_792,c_685])).

tff(c_884,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_883])).

tff(c_291,plain,(
    ! [A_96,B_97,C_98] : k2_zfmisc_1(k2_zfmisc_1(A_96,B_97),C_98) = k3_zfmisc_1(A_96,B_97,C_98) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    ! [A_28,C_30,B_29] :
      ( r2_hidden(k2_mcart_1(A_28),C_30)
      | ~ r2_hidden(A_28,k2_zfmisc_1(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_487,plain,(
    ! [A_128,C_129,A_130,B_131] :
      ( r2_hidden(k2_mcart_1(A_128),C_129)
      | ~ r2_hidden(A_128,k3_zfmisc_1(A_130,B_131,C_129)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_36])).

tff(c_509,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_487])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_528,plain,(
    ! [B_135] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_135)
      | ~ r1_tarski('#skF_9',B_135) ) ),
    inference(resolution,[status(thm)],[c_509,c_6])).

tff(c_627,plain,(
    ! [B_155,B_156] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_155)
      | ~ r1_tarski(B_156,B_155)
      | ~ r1_tarski('#skF_9',B_156) ) ),
    inference(resolution,[status(thm)],[c_528,c_6])).

tff(c_647,plain,(
    ! [A_17] :
      ( r2_hidden(k2_mcart_1('#skF_10'),A_17)
      | ~ r1_tarski('#skF_9',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_627])).

tff(c_678,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_889,plain,(
    ~ r1_tarski('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_678])).

tff(c_899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_889])).

tff(c_900,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_883])).

tff(c_38,plain,(
    ! [A_28,B_29,C_30] :
      ( r2_hidden(k1_mcart_1(A_28),B_29)
      | ~ r2_hidden(A_28,k2_zfmisc_1(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2073,plain,(
    ! [A_283,A_284,B_285,C_286] :
      ( r2_hidden(k1_mcart_1(A_283),k2_zfmisc_1(A_284,B_285))
      | ~ r2_hidden(A_283,k3_zfmisc_1(A_284,B_285,C_286)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_38])).

tff(c_2138,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_2073])).

tff(c_2147,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2138,c_38])).

tff(c_2158,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_2147])).

tff(c_2160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2158])).

tff(c_2162,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_552,plain,(
    ! [B_135] :
      ( ~ v1_xboole_0(B_135)
      | ~ r1_tarski('#skF_9',B_135) ) ),
    inference(resolution,[status(thm)],[c_528,c_2])).

tff(c_2167,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2162,c_552])).

tff(c_2185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_2167])).

tff(c_2186,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_2188,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_96])).

tff(c_2191,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_48])).

tff(c_2599,plain,(
    ! [A_345,B_346,C_347,D_348] :
      ( k7_mcart_1(A_345,B_346,C_347,D_348) = k2_mcart_1(D_348)
      | ~ m1_subset_1(D_348,k3_zfmisc_1(A_345,B_346,C_347))
      | k1_xboole_0 = C_347
      | k1_xboole_0 = B_346
      | k1_xboole_0 = A_345 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2603,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_2599])).

tff(c_2621,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2603])).

tff(c_2626,plain,(
    ! [A_17] : r1_tarski('#skF_4',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2621,c_24])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),A_10)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2284,plain,(
    ! [C_300,B_301,A_302] :
      ( r2_hidden(C_300,B_301)
      | ~ r2_hidden(C_300,A_302)
      | ~ r1_tarski(A_302,B_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2816,plain,(
    ! [A_383,B_384,B_385] :
      ( r2_hidden('#skF_3'(A_383,B_384),B_385)
      | ~ r1_tarski(A_383,B_385)
      | r1_xboole_0(A_383,B_384) ) ),
    inference(resolution,[status(thm)],[c_16,c_2284])).

tff(c_2841,plain,(
    ! [B_386,A_387,B_388] :
      ( ~ v1_xboole_0(B_386)
      | ~ r1_tarski(A_387,B_386)
      | r1_xboole_0(A_387,B_388) ) ),
    inference(resolution,[status(thm)],[c_2816,c_2])).

tff(c_2852,plain,(
    ! [A_17,B_388] :
      ( ~ v1_xboole_0(A_17)
      | r1_xboole_0('#skF_4',B_388) ) ),
    inference(resolution,[status(thm)],[c_2626,c_2841])).

tff(c_2857,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_2852])).

tff(c_2331,plain,(
    ! [A_309,B_310] :
      ( r2_hidden('#skF_1'(A_309),B_310)
      | ~ r1_tarski(A_309,B_310)
      | v1_xboole_0(A_309) ) ),
    inference(resolution,[status(thm)],[c_4,c_2284])).

tff(c_2352,plain,(
    ! [B_311,A_312] :
      ( ~ v1_xboole_0(B_311)
      | ~ r1_tarski(A_312,B_311)
      | v1_xboole_0(A_312) ) ),
    inference(resolution,[status(thm)],[c_2331,c_2])).

tff(c_2372,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_2352])).

tff(c_2373,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_2372])).

tff(c_2479,plain,(
    ! [A_329,B_330,C_331] :
      ( ~ r1_xboole_0(A_329,B_330)
      | ~ r1_tarski(C_331,B_330)
      | ~ r1_tarski(C_331,A_329) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2373,c_26])).

tff(c_2483,plain,(
    ! [C_332,B_333,A_334] :
      ( ~ r1_tarski(C_332,B_333)
      | ~ r1_tarski(C_332,k4_xboole_0(A_334,B_333)) ) ),
    inference(resolution,[status(thm)],[c_28,c_2479])).

tff(c_2491,plain,(
    ! [B_333] : ~ r1_tarski(k1_xboole_0,B_333) ),
    inference(resolution,[status(thm)],[c_24,c_2483])).

tff(c_2496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2491])).

tff(c_2497,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2372])).

tff(c_2623,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2621,c_2497])).

tff(c_2866,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2857,c_2623])).

tff(c_2873,plain,(
    ! [B_392] : r1_xboole_0('#skF_4',B_392) ),
    inference(splitRight,[status(thm)],[c_2852])).

tff(c_12,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,B_11)
      | ~ r2_hidden(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2880,plain,(
    ! [C_393,B_394] :
      ( ~ r2_hidden(C_393,B_394)
      | ~ r2_hidden(C_393,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2873,c_12])).

tff(c_2909,plain,(
    ~ r2_hidden('#skF_10','#skF_4') ),
    inference(resolution,[status(thm)],[c_2191,c_2880])).

tff(c_2231,plain,(
    ! [A_291,B_292,C_293] :
      ( r2_hidden(k1_mcart_1(A_291),B_292)
      | ~ r2_hidden(A_291,k2_zfmisc_1(B_292,C_293)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3061,plain,(
    ! [B_406,C_407] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_406,C_407))),B_406)
      | v1_xboole_0(k2_zfmisc_1(B_406,C_407)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2231])).

tff(c_3099,plain,(
    ! [B_408,C_409] :
      ( ~ v1_xboole_0(B_408)
      | v1_xboole_0(k2_zfmisc_1(B_408,C_409)) ) ),
    inference(resolution,[status(thm)],[c_3061,c_2])).

tff(c_131,plain,(
    ! [A_70] :
      ( k1_xboole_0 = A_70
      | ~ r1_tarski(A_70,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_109])).

tff(c_144,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_107,c_131])).

tff(c_2624,plain,(
    ! [A_64] :
      ( A_64 = '#skF_4'
      | ~ v1_xboole_0(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2621,c_144])).

tff(c_3117,plain,(
    ! [B_410,C_411] :
      ( k2_zfmisc_1(B_410,C_411) = '#skF_4'
      | ~ v1_xboole_0(B_410) ) ),
    inference(resolution,[status(thm)],[c_3099,c_2624])).

tff(c_3128,plain,(
    ! [C_411] : k2_zfmisc_1('#skF_4',C_411) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2623,c_3117])).

tff(c_3129,plain,(
    ! [C_412] : k2_zfmisc_1('#skF_4',C_412) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2623,c_3117])).

tff(c_3155,plain,(
    ! [C_412,C_27] : k3_zfmisc_1('#skF_4',C_412,C_27) = k2_zfmisc_1('#skF_4',C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_3129,c_34])).

tff(c_3170,plain,(
    ! [C_412,C_27] : k3_zfmisc_1('#skF_4',C_412,C_27) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3128,c_3155])).

tff(c_3174,plain,(
    r2_hidden('#skF_10','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3170,c_2191])).

tff(c_3180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2909,c_3174])).

tff(c_3182,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2603])).

tff(c_3302,plain,(
    ! [A_429,B_430,C_431,D_432] :
      ( k6_mcart_1(A_429,B_430,C_431,D_432) = k2_mcart_1(k1_mcart_1(D_432))
      | ~ m1_subset_1(D_432,k3_zfmisc_1(A_429,B_430,C_431))
      | k1_xboole_0 = C_431
      | k1_xboole_0 = B_430
      | k1_xboole_0 = A_429 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3305,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_3302])).

tff(c_3308,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3182,c_3305])).

tff(c_3411,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3308])).

tff(c_3417,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3411,c_2497])).

tff(c_3422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_3417])).

tff(c_3424,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3308])).

tff(c_3213,plain,(
    ! [A_420,B_421,C_422,D_423] :
      ( k5_mcart_1(A_420,B_421,C_422,D_423) = k1_mcart_1(k1_mcart_1(D_423))
      | ~ m1_subset_1(D_423,k3_zfmisc_1(A_420,B_421,C_422))
      | k1_xboole_0 = C_422
      | k1_xboole_0 = B_421
      | k1_xboole_0 = A_420 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3216,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_3213])).

tff(c_3219,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3182,c_3216])).

tff(c_3479,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_3424,c_3219])).

tff(c_3480,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3479])).

tff(c_2265,plain,(
    ! [A_297,C_298,B_299] :
      ( r2_hidden(k2_mcart_1(A_297),C_298)
      | ~ r2_hidden(A_297,k2_zfmisc_1(B_299,C_298)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2528,plain,(
    ! [A_339,C_340,A_341,B_342] :
      ( r2_hidden(k2_mcart_1(A_339),C_340)
      | ~ r2_hidden(A_339,k3_zfmisc_1(A_341,B_342,C_340)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2265])).

tff(c_2547,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_2191,c_2528])).

tff(c_2559,plain,(
    ! [B_343] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_343)
      | ~ r1_tarski('#skF_9',B_343) ) ),
    inference(resolution,[status(thm)],[c_2547,c_6])).

tff(c_3220,plain,(
    ! [B_424,B_425] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_424)
      | ~ r1_tarski(B_425,B_424)
      | ~ r1_tarski('#skF_9',B_425) ) ),
    inference(resolution,[status(thm)],[c_2559,c_6])).

tff(c_3226,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_6')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_3220])).

tff(c_3235,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3226])).

tff(c_3246,plain,(
    ! [B_6] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_6)
      | ~ r1_tarski('#skF_6',B_6) ) ),
    inference(resolution,[status(thm)],[c_3235,c_6])).

tff(c_3359,plain,(
    ! [A_445,B_446,B_447] :
      ( r2_hidden('#skF_3'(A_445,B_446),B_447)
      | ~ r1_tarski(A_445,B_447)
      | r1_xboole_0(A_445,B_446) ) ),
    inference(resolution,[status(thm)],[c_16,c_2284])).

tff(c_3384,plain,(
    ! [B_448,A_449,B_450] :
      ( ~ v1_xboole_0(B_448)
      | ~ r1_tarski(A_449,B_448)
      | r1_xboole_0(A_449,B_450) ) ),
    inference(resolution,[status(thm)],[c_3359,c_2])).

tff(c_3399,plain,(
    ! [A_17,B_450] :
      ( ~ v1_xboole_0(A_17)
      | r1_xboole_0(k1_xboole_0,B_450) ) ),
    inference(resolution,[status(thm)],[c_24,c_3384])).

tff(c_3400,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_3399])).

tff(c_3409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3400,c_2497])).

tff(c_3425,plain,(
    ! [B_451] : r1_xboole_0(k1_xboole_0,B_451) ),
    inference(splitRight,[status(thm)],[c_3399])).

tff(c_3432,plain,(
    ! [C_452,B_453] :
      ( ~ r2_hidden(C_452,B_453)
      | ~ r2_hidden(C_452,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_3425,c_12])).

tff(c_3459,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2547,c_3432])).

tff(c_3473,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3246,c_3459])).

tff(c_3481,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3480,c_3473])).

tff(c_3498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_3481])).

tff(c_3499,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_3479])).

tff(c_2248,plain,(
    ! [A_294,B_295,C_296] : k2_zfmisc_1(k2_zfmisc_1(A_294,B_295),C_296) = k3_zfmisc_1(A_294,B_295,C_296) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4571,plain,(
    ! [A_546,A_547,B_548,C_549] :
      ( r2_hidden(k1_mcart_1(A_546),k2_zfmisc_1(A_547,B_548))
      | ~ r2_hidden(A_546,k3_zfmisc_1(A_547,B_548,C_549)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2248,c_38])).

tff(c_4631,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_2191,c_4571])).

tff(c_4641,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_4631,c_38])).

tff(c_4649,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3499,c_4641])).

tff(c_4651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2188,c_4649])).

tff(c_4652,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_4654,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4652,c_96])).

tff(c_4674,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_4678,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_4674])).

tff(c_4656,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4652,c_50])).

tff(c_5018,plain,(
    ! [A_606,B_607,C_608,D_609] :
      ( k7_mcart_1(A_606,B_607,C_608,D_609) = k2_mcart_1(D_609)
      | ~ m1_subset_1(D_609,k3_zfmisc_1(A_606,B_607,C_608))
      | k1_xboole_0 = C_608
      | k1_xboole_0 = B_607
      | k1_xboole_0 = A_606 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5022,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4656,c_5018])).

tff(c_5063,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5022])).

tff(c_4786,plain,(
    ! [C_569,B_570,A_571] :
      ( r2_hidden(C_569,B_570)
      | ~ r2_hidden(C_569,A_571)
      | ~ r1_tarski(A_571,B_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4814,plain,(
    ! [A_573,B_574] :
      ( r2_hidden('#skF_1'(A_573),B_574)
      | ~ r1_tarski(A_573,B_574)
      | v1_xboole_0(A_573) ) ),
    inference(resolution,[status(thm)],[c_4,c_4786])).

tff(c_4835,plain,(
    ! [B_575,A_576] :
      ( ~ v1_xboole_0(B_575)
      | ~ r1_tarski(A_576,B_575)
      | v1_xboole_0(A_576) ) ),
    inference(resolution,[status(thm)],[c_4814,c_2])).

tff(c_4855,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_4835])).

tff(c_4866,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_4855])).

tff(c_4912,plain,(
    ! [A_586,B_587,C_588] :
      ( ~ r1_xboole_0(A_586,B_587)
      | ~ r1_tarski(C_588,B_587)
      | ~ r1_tarski(C_588,A_586) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4866,c_26])).

tff(c_4964,plain,(
    ! [C_599,B_600,A_601] :
      ( ~ r1_tarski(C_599,B_600)
      | ~ r1_tarski(C_599,k4_xboole_0(A_601,B_600)) ) ),
    inference(resolution,[status(thm)],[c_28,c_4912])).

tff(c_4972,plain,(
    ! [B_600] : ~ r1_tarski(k1_xboole_0,B_600) ),
    inference(resolution,[status(thm)],[c_24,c_4964])).

tff(c_4977,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4972])).

tff(c_4978,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_4855])).

tff(c_5065,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5063,c_4978])).

tff(c_5070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4678,c_5065])).

tff(c_5072,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5022])).

tff(c_5166,plain,(
    ! [A_631,B_632,C_633,D_634] :
      ( k6_mcart_1(A_631,B_632,C_633,D_634) = k2_mcart_1(k1_mcart_1(D_634))
      | ~ m1_subset_1(D_634,k3_zfmisc_1(A_631,B_632,C_633))
      | k1_xboole_0 = C_633
      | k1_xboole_0 = B_632
      | k1_xboole_0 = A_631 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5169,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4656,c_5166])).

tff(c_5172,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_5072,c_5169])).

tff(c_5787,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_5172])).

tff(c_4748,plain,(
    ! [A_563,C_564,B_565] :
      ( r2_hidden(k2_mcart_1(A_563),C_564)
      | ~ r2_hidden(A_563,k2_zfmisc_1(B_565,C_564)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_5256,plain,(
    ! [B_647,C_648] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_647,C_648))),C_648)
      | v1_xboole_0(k2_zfmisc_1(B_647,C_648)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4748])).

tff(c_5285,plain,(
    ! [C_649,B_650] :
      ( ~ v1_xboole_0(C_649)
      | v1_xboole_0(k2_zfmisc_1(B_650,C_649)) ) ),
    inference(resolution,[status(thm)],[c_5256,c_2])).

tff(c_5296,plain,(
    ! [B_651,C_652] :
      ( k2_zfmisc_1(B_651,C_652) = k1_xboole_0
      | ~ v1_xboole_0(C_652) ) ),
    inference(resolution,[status(thm)],[c_5285,c_144])).

tff(c_5303,plain,(
    ! [B_653] : k2_zfmisc_1(B_653,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4978,c_5296])).

tff(c_5398,plain,(
    ! [A_664] :
      ( r2_hidden(k2_mcart_1(A_664),k1_xboole_0)
      | ~ r2_hidden(A_664,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5303,c_36])).

tff(c_5409,plain,(
    ! [A_664] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_664,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_5398,c_2])).

tff(c_5417,plain,(
    ! [A_664] : ~ r2_hidden(A_664,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4978,c_5409])).

tff(c_5797,plain,(
    ! [A_664] : ~ r2_hidden(A_664,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5787,c_5417])).

tff(c_5302,plain,(
    ! [B_651] : k2_zfmisc_1(B_651,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4978,c_5296])).

tff(c_5800,plain,(
    ! [B_651] : k2_zfmisc_1(B_651,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5787,c_5787,c_5302])).

tff(c_4767,plain,(
    ! [A_566,B_567,C_568] :
      ( r2_hidden(k1_mcart_1(A_566),B_567)
      | ~ r2_hidden(A_566,k2_zfmisc_1(B_567,C_568)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6207,plain,(
    ! [A_724,A_725,B_726,C_727] :
      ( r2_hidden(k1_mcart_1(A_724),k2_zfmisc_1(A_725,B_726))
      | ~ r2_hidden(A_724,k3_zfmisc_1(A_725,B_726,C_727)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4767])).

tff(c_6248,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_6207])).

tff(c_6267,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5800,c_6248])).

tff(c_6269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5797,c_6267])).

tff(c_6271,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5172])).

tff(c_5090,plain,(
    ! [A_617,B_618,C_619,D_620] :
      ( k5_mcart_1(A_617,B_618,C_619,D_620) = k1_mcart_1(k1_mcart_1(D_620))
      | ~ m1_subset_1(D_620,k3_zfmisc_1(A_617,B_618,C_619))
      | k1_xboole_0 = C_619
      | k1_xboole_0 = B_618
      | k1_xboole_0 = A_617 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5093,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4656,c_5090])).

tff(c_5096,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_5072,c_5093])).

tff(c_6277,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_6271,c_5096])).

tff(c_6278,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6277])).

tff(c_4987,plain,(
    ! [A_602,C_603,A_604,B_605] :
      ( r2_hidden(k2_mcart_1(A_602),C_603)
      | ~ r2_hidden(A_602,k3_zfmisc_1(A_604,B_605,C_603)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4748])).

tff(c_5009,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_4987])).

tff(c_5023,plain,(
    ! [B_610] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_610)
      | ~ r1_tarski('#skF_9',B_610) ) ),
    inference(resolution,[status(thm)],[c_5009,c_6])).

tff(c_5127,plain,(
    ! [B_628,B_629] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_628)
      | ~ r1_tarski(B_629,B_628)
      | ~ r1_tarski('#skF_9',B_629) ) ),
    inference(resolution,[status(thm)],[c_5023,c_6])).

tff(c_5133,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_6')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_5127])).

tff(c_5142,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_5133])).

tff(c_5153,plain,(
    ! [B_6] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_6)
      | ~ r1_tarski('#skF_6',B_6) ) ),
    inference(resolution,[status(thm)],[c_5142,c_6])).

tff(c_5444,plain,(
    ! [A_668] : ~ r2_hidden(A_668,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4978,c_5409])).

tff(c_5484,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_5153,c_5444])).

tff(c_6288,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6278,c_5484])).

tff(c_6305,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6288])).

tff(c_6306,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_6277])).

tff(c_7279,plain,(
    ! [A_787,A_788,B_789,C_790] :
      ( r2_hidden(k1_mcart_1(A_787),k2_zfmisc_1(A_788,B_789))
      | ~ r2_hidden(A_787,k3_zfmisc_1(A_788,B_789,C_790)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4767])).

tff(c_7344,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_7279])).

tff(c_7349,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_7344,c_38])).

tff(c_7357,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6306,c_7349])).

tff(c_7359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4654,c_7357])).

tff(c_7360,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_7416,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7360,c_4654])).

tff(c_7364,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7360,c_48])).

tff(c_7682,plain,(
    ! [A_843,B_844,C_845,D_846] :
      ( k7_mcart_1(A_843,B_844,C_845,D_846) = k2_mcart_1(D_846)
      | ~ m1_subset_1(D_846,k3_zfmisc_1(A_843,B_844,C_845))
      | k1_xboole_0 = C_845
      | k1_xboole_0 = B_844
      | k1_xboole_0 = A_843 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_7686,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4656,c_7682])).

tff(c_7780,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_7686])).

tff(c_7786,plain,(
    ! [A_17] : r1_tarski('#skF_4',A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7780,c_24])).

tff(c_7883,plain,(
    ! [A_880,B_881,B_882] :
      ( r2_hidden('#skF_3'(A_880,B_881),B_882)
      | ~ r1_tarski(A_880,B_882)
      | r1_xboole_0(A_880,B_881) ) ),
    inference(resolution,[status(thm)],[c_16,c_7400])).

tff(c_7908,plain,(
    ! [B_883,A_884,B_885] :
      ( ~ v1_xboole_0(B_883)
      | ~ r1_tarski(A_884,B_883)
      | r1_xboole_0(A_884,B_885) ) ),
    inference(resolution,[status(thm)],[c_7883,c_2])).

tff(c_7917,plain,(
    ! [A_17,B_885] :
      ( ~ v1_xboole_0(A_17)
      | r1_xboole_0('#skF_4',B_885) ) ),
    inference(resolution,[status(thm)],[c_7786,c_7908])).

tff(c_7921,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_7917])).

tff(c_7783,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7780,c_7673])).

tff(c_7930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7921,c_7783])).

tff(c_7947,plain,(
    ! [B_888] : r1_xboole_0('#skF_4',B_888) ),
    inference(splitRight,[status(thm)],[c_7917])).

tff(c_7969,plain,(
    ! [C_890,B_891] :
      ( ~ r2_hidden(C_890,B_891)
      | ~ r2_hidden(C_890,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7947,c_12])).

tff(c_7995,plain,(
    ~ r2_hidden('#skF_10','#skF_4') ),
    inference(resolution,[status(thm)],[c_7364,c_7969])).

tff(c_7463,plain,(
    ! [A_805,B_806,C_807] :
      ( r2_hidden(k1_mcart_1(A_805),B_806)
      | ~ r2_hidden(A_805,k2_zfmisc_1(B_806,C_807)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8253,plain,(
    ! [B_917,C_918] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_917,C_918))),B_917)
      | v1_xboole_0(k2_zfmisc_1(B_917,C_918)) ) ),
    inference(resolution,[status(thm)],[c_4,c_7463])).

tff(c_8291,plain,(
    ! [B_919,C_920] :
      ( ~ v1_xboole_0(B_919)
      | v1_xboole_0(k2_zfmisc_1(B_919,C_920)) ) ),
    inference(resolution,[status(thm)],[c_8253,c_2])).

tff(c_7784,plain,(
    ! [A_64] :
      ( A_64 = '#skF_4'
      | ~ v1_xboole_0(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7780,c_144])).

tff(c_8312,plain,(
    ! [B_921,C_922] :
      ( k2_zfmisc_1(B_921,C_922) = '#skF_4'
      | ~ v1_xboole_0(B_921) ) ),
    inference(resolution,[status(thm)],[c_8291,c_7784])).

tff(c_8326,plain,(
    ! [C_922] : k2_zfmisc_1('#skF_4',C_922) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7783,c_8312])).

tff(c_8327,plain,(
    ! [C_923] : k2_zfmisc_1('#skF_4',C_923) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7783,c_8312])).

tff(c_8353,plain,(
    ! [C_923,C_27] : k3_zfmisc_1('#skF_4',C_923,C_27) = k2_zfmisc_1('#skF_4',C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_8327,c_34])).

tff(c_8368,plain,(
    ! [C_923,C_27] : k3_zfmisc_1('#skF_4',C_923,C_27) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8326,c_8353])).

tff(c_8377,plain,(
    r2_hidden('#skF_10','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8368,c_7364])).

tff(c_8383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7995,c_8377])).

tff(c_8385,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7686])).

tff(c_7758,plain,(
    ! [A_853,B_854,C_855,D_856] :
      ( k5_mcart_1(A_853,B_854,C_855,D_856) = k1_mcart_1(k1_mcart_1(D_856))
      | ~ m1_subset_1(D_856,k3_zfmisc_1(A_853,B_854,C_855))
      | k1_xboole_0 = C_855
      | k1_xboole_0 = B_854
      | k1_xboole_0 = A_853 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_7762,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4656,c_7758])).

tff(c_8452,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_8385,c_7762])).

tff(c_8453,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_8452])).

tff(c_8458,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8453,c_7673])).

tff(c_7417,plain,(
    ! [A_798,C_799,B_800] :
      ( r2_hidden(k2_mcart_1(A_798),C_799)
      | ~ r2_hidden(A_798,k2_zfmisc_1(B_800,C_799)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8498,plain,(
    ! [B_945,C_946] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_945,C_946))),C_946)
      | v1_xboole_0(k2_zfmisc_1(B_945,C_946)) ) ),
    inference(resolution,[status(thm)],[c_4,c_7417])).

tff(c_8561,plain,(
    ! [C_949,B_950] :
      ( ~ v1_xboole_0(C_949)
      | v1_xboole_0(k2_zfmisc_1(B_950,C_949)) ) ),
    inference(resolution,[status(thm)],[c_8498,c_2])).

tff(c_8459,plain,(
    ! [A_64] :
      ( A_64 = '#skF_8'
      | ~ v1_xboole_0(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8453,c_144])).

tff(c_8572,plain,(
    ! [B_951,C_952] :
      ( k2_zfmisc_1(B_951,C_952) = '#skF_8'
      | ~ v1_xboole_0(C_952) ) ),
    inference(resolution,[status(thm)],[c_8561,c_8459])).

tff(c_8609,plain,(
    ! [B_956] : k2_zfmisc_1(B_956,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_8458,c_8572])).

tff(c_8692,plain,(
    ! [A_965] :
      ( r2_hidden(k2_mcart_1(A_965),'#skF_8')
      | ~ r2_hidden(A_965,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8609,c_36])).

tff(c_8700,plain,(
    ! [A_965] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_965,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8692,c_2])).

tff(c_8707,plain,(
    ! [A_965] : ~ r2_hidden(A_965,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8458,c_8700])).

tff(c_8525,plain,(
    ! [C_946,B_945] :
      ( ~ v1_xboole_0(C_946)
      | v1_xboole_0(k2_zfmisc_1(B_945,C_946)) ) ),
    inference(resolution,[status(thm)],[c_8498,c_2])).

tff(c_8885,plain,(
    ! [B_979,C_980] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_979,C_980))),B_979)
      | v1_xboole_0(k2_zfmisc_1(B_979,C_980)) ) ),
    inference(resolution,[status(thm)],[c_4,c_7463])).

tff(c_9018,plain,(
    ! [B_988,C_989] :
      ( ~ v1_xboole_0(B_988)
      | v1_xboole_0(k2_zfmisc_1(B_988,C_989)) ) ),
    inference(resolution,[status(thm)],[c_8885,c_2])).

tff(c_9044,plain,(
    ! [B_990,C_991] :
      ( k2_zfmisc_1(B_990,C_991) = '#skF_8'
      | ~ v1_xboole_0(B_990) ) ),
    inference(resolution,[status(thm)],[c_9018,c_8459])).

tff(c_9050,plain,(
    ! [B_945,C_946,C_991] :
      ( k2_zfmisc_1(k2_zfmisc_1(B_945,C_946),C_991) = '#skF_8'
      | ~ v1_xboole_0(C_946) ) ),
    inference(resolution,[status(thm)],[c_8525,c_9044])).

tff(c_9113,plain,(
    ! [B_1000,C_1001,C_1002] :
      ( k3_zfmisc_1(B_1000,C_1001,C_1002) = '#skF_8'
      | ~ v1_xboole_0(C_1001) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_9050])).

tff(c_9125,plain,(
    ! [B_1000,C_1002] : k3_zfmisc_1(B_1000,'#skF_8',C_1002) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_8458,c_9113])).

tff(c_9127,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9125,c_7364])).

tff(c_9133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8707,c_9127])).

tff(c_9135,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_8452])).

tff(c_8416,plain,(
    ! [A_933,B_934,C_935,D_936] :
      ( k6_mcart_1(A_933,B_934,C_935,D_936) = k2_mcart_1(k1_mcart_1(D_936))
      | ~ m1_subset_1(D_936,k3_zfmisc_1(A_933,B_934,C_935))
      | k1_xboole_0 = C_935
      | k1_xboole_0 = B_934
      | k1_xboole_0 = A_933 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_8419,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4656,c_8416])).

tff(c_8422,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_8385,c_8419])).

tff(c_9409,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_9135,c_8422])).

tff(c_9410,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_9409])).

tff(c_7434,plain,(
    ! [A_801,B_802,C_803] : k2_zfmisc_1(k2_zfmisc_1(A_801,B_802),C_803) = k3_zfmisc_1(A_801,B_802,C_803) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7687,plain,(
    ! [A_847,C_848,A_849,B_850] :
      ( r2_hidden(k2_mcart_1(A_847),C_848)
      | ~ r2_hidden(A_847,k3_zfmisc_1(A_849,B_850,C_848)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7434,c_36])).

tff(c_7706,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_7364,c_7687])).

tff(c_7718,plain,(
    ! [B_851] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_851)
      | ~ r1_tarski('#skF_9',B_851) ) ),
    inference(resolution,[status(thm)],[c_7706,c_6])).

tff(c_8437,plain,(
    ! [B_941,B_942] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_941)
      | ~ r1_tarski(B_942,B_941)
      | ~ r1_tarski('#skF_9',B_942) ) ),
    inference(resolution,[status(thm)],[c_7718,c_6])).

tff(c_8451,plain,(
    ! [A_17] :
      ( r2_hidden(k2_mcart_1('#skF_10'),A_17)
      | ~ r1_tarski('#skF_9',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_8437])).

tff(c_9151,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_8451])).

tff(c_9418,plain,(
    ~ r1_tarski('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9410,c_9151])).

tff(c_9430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_9418])).

tff(c_9432,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9409])).

tff(c_9134,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_8452])).

tff(c_9512,plain,(
    k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_9432,c_9134])).

tff(c_10273,plain,(
    ! [A_1102,A_1103,B_1104,C_1105] :
      ( r2_hidden(k1_mcart_1(A_1102),k2_zfmisc_1(A_1103,B_1104))
      | ~ r2_hidden(A_1102,k3_zfmisc_1(A_1103,B_1104,C_1105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_7463])).

tff(c_10333,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_7364,c_10273])).

tff(c_10339,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_10333,c_38])).

tff(c_10348,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9512,c_10339])).

tff(c_10350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7416,c_10348])).

tff(c_10352,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_8451])).

tff(c_7742,plain,(
    ! [B_851] :
      ( ~ v1_xboole_0(B_851)
      | ~ r1_tarski('#skF_9',B_851) ) ),
    inference(resolution,[status(thm)],[c_7718,c_2])).

tff(c_10357,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10352,c_7742])).

tff(c_10375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7673,c_10357])).

tff(c_10376,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8')
    | ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_10382,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_10376])).

tff(c_11082,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11081,c_10382])).

tff(c_11085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10883,c_11082])).

tff(c_11086,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10952])).

tff(c_11088,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_11086])).

tff(c_11094,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11088,c_10782])).

tff(c_11099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10444,c_11094])).

tff(c_11100,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11086])).

tff(c_10897,plain,(
    ! [B_1189] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1189)
      | ~ r1_tarski('#skF_9',B_1189) ) ),
    inference(resolution,[status(thm)],[c_10883,c_6])).

tff(c_10984,plain,(
    ! [B_1204,B_1205] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1204)
      | ~ r1_tarski(B_1205,B_1204)
      | ~ r1_tarski('#skF_9',B_1205) ) ),
    inference(resolution,[status(thm)],[c_10897,c_6])).

tff(c_11004,plain,(
    ! [A_17] :
      ( r2_hidden(k2_mcart_1('#skF_10'),A_17)
      | ~ r1_tarski('#skF_9',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_10984])).

tff(c_11025,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11004])).

tff(c_11104,plain,(
    ~ r1_tarski('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11100,c_11025])).

tff(c_11114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_11104])).

tff(c_11116,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11004])).

tff(c_10921,plain,(
    ! [B_1189] :
      ( ~ v1_xboole_0(B_1189)
      | ~ r1_tarski('#skF_9',B_1189) ) ),
    inference(resolution,[status(thm)],[c_10897,c_2])).

tff(c_11128,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11116,c_10921])).

tff(c_11146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10782,c_11128])).

tff(c_11147,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10394])).

tff(c_11153,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11147,c_48])).

tff(c_11299,plain,(
    ! [A_1241,C_1242,B_1243] :
      ( r2_hidden(k2_mcart_1(A_1241),C_1242)
      | ~ r2_hidden(A_1241,k2_zfmisc_1(B_1243,C_1242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_11515,plain,(
    ! [A_1273,C_1274,A_1275,B_1276] :
      ( r2_hidden(k2_mcart_1(A_1273),C_1274)
      | ~ r2_hidden(A_1273,k3_zfmisc_1(A_1275,B_1276,C_1274)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_11299])).

tff(c_11535,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_11153,c_11515])).

tff(c_10377,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_10381,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_10377,c_2])).

tff(c_11149,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11147,c_10381])).

tff(c_11539,plain,(
    ! [A_1277,B_1278,C_1279,D_1280] :
      ( k7_mcart_1(A_1277,B_1278,C_1279,D_1280) = k2_mcart_1(D_1280)
      | ~ m1_subset_1(D_1280,k3_zfmisc_1(A_1277,B_1278,C_1279))
      | k1_xboole_0 = C_1279
      | k1_xboole_0 = B_1278
      | k1_xboole_0 = A_1277 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_11543,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_11539])).

tff(c_11576,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_11543])).

tff(c_11203,plain,(
    ! [C_1225,B_1226,A_1227] :
      ( r2_hidden(C_1225,B_1226)
      | ~ r2_hidden(C_1225,A_1227)
      | ~ r1_tarski(A_1227,B_1226) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11328,plain,(
    ! [A_1247,B_1248] :
      ( r2_hidden('#skF_1'(A_1247),B_1248)
      | ~ r1_tarski(A_1247,B_1248)
      | v1_xboole_0(A_1247) ) ),
    inference(resolution,[status(thm)],[c_4,c_11203])).

tff(c_11349,plain,(
    ! [B_1249,A_1250] :
      ( ~ v1_xboole_0(B_1249)
      | ~ r1_tarski(A_1250,B_1249)
      | v1_xboole_0(A_1250) ) ),
    inference(resolution,[status(thm)],[c_11328,c_2])).

tff(c_11369,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_11349])).

tff(c_11370,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_11369])).

tff(c_11437,plain,(
    ! [A_1258,B_1259,C_1260] :
      ( ~ r1_xboole_0(A_1258,B_1259)
      | ~ r1_tarski(C_1260,B_1259)
      | ~ r1_tarski(C_1260,A_1258) ) ),
    inference(negUnitSimplification,[status(thm)],[c_11370,c_26])).

tff(c_11492,plain,(
    ! [C_1270,B_1271,A_1272] :
      ( ~ r1_tarski(C_1270,B_1271)
      | ~ r1_tarski(C_1270,k4_xboole_0(A_1272,B_1271)) ) ),
    inference(resolution,[status(thm)],[c_28,c_11437])).

tff(c_11500,plain,(
    ! [B_1271] : ~ r1_tarski(k1_xboole_0,B_1271) ),
    inference(resolution,[status(thm)],[c_24,c_11492])).

tff(c_11505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_11500])).

tff(c_11506,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11369])).

tff(c_11578,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11576,c_11506])).

tff(c_11583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11149,c_11578])).

tff(c_11584,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_11543])).

tff(c_11649,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_11584])).

tff(c_11650,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11649,c_10382])).

tff(c_11653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11535,c_11650])).

tff(c_11654,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_11584])).

tff(c_11656,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_11654])).

tff(c_11660,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11656,c_11506])).

tff(c_11665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10444,c_11660])).

tff(c_11666,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11654])).

tff(c_11672,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11666,c_11506])).

tff(c_11677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10437,c_11672])).

tff(c_11678,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_10395])).

tff(c_11688,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11678,c_50])).

tff(c_12048,plain,(
    ! [A_1354,B_1355,C_1356,D_1357] :
      ( k7_mcart_1(A_1354,B_1355,C_1356,D_1357) = k2_mcart_1(D_1357)
      | ~ m1_subset_1(D_1357,k3_zfmisc_1(A_1354,B_1355,C_1356))
      | k1_xboole_0 = C_1356
      | k1_xboole_0 = B_1355
      | k1_xboole_0 = A_1354 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12052,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11688,c_12048])).

tff(c_12092,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_12052])).

tff(c_12094,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12092,c_12039])).

tff(c_12099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11707,c_12094])).

tff(c_12100,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_12052])).

tff(c_12488,plain,(
    k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_12100])).

tff(c_11685,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11678,c_10382])).

tff(c_12496,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12488,c_11685])).

tff(c_12499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12128,c_12496])).

tff(c_12500,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_12100])).

tff(c_12509,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_12500])).

tff(c_12520,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12509,c_12039])).

tff(c_11781,plain,(
    ! [A_1313,B_1314,C_1315] :
      ( r2_hidden(k1_mcart_1(A_1313),B_1314)
      | ~ r2_hidden(A_1313,k2_zfmisc_1(B_1314,C_1315)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_12733,plain,(
    ! [B_1430,C_1431] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1430,C_1431))),B_1430)
      | v1_xboole_0(k2_zfmisc_1(B_1430,C_1431)) ) ),
    inference(resolution,[status(thm)],[c_4,c_11781])).

tff(c_12775,plain,(
    ! [B_1432,C_1433] :
      ( ~ v1_xboole_0(B_1432)
      | v1_xboole_0(k2_zfmisc_1(B_1432,C_1433)) ) ),
    inference(resolution,[status(thm)],[c_12733,c_2])).

tff(c_10401,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_10383])).

tff(c_10438,plain,(
    ! [A_1111] :
      ( k1_xboole_0 = A_1111
      | ~ v1_xboole_0(A_1111) ) ),
    inference(resolution,[status(thm)],[c_10427,c_10401])).

tff(c_12521,plain,(
    ! [A_1111] :
      ( A_1111 = '#skF_8'
      | ~ v1_xboole_0(A_1111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12509,c_10438])).

tff(c_12843,plain,(
    ! [B_1436,C_1437] :
      ( k2_zfmisc_1(B_1436,C_1437) = '#skF_8'
      | ~ v1_xboole_0(B_1436) ) ),
    inference(resolution,[status(thm)],[c_12775,c_12521])).

tff(c_12854,plain,(
    ! [C_1437] : k2_zfmisc_1('#skF_8',C_1437) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_12520,c_12843])).

tff(c_12528,plain,(
    ! [B_1413,C_1414] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1413,C_1414))),C_1414)
      | v1_xboole_0(k2_zfmisc_1(B_1413,C_1414)) ) ),
    inference(resolution,[status(thm)],[c_4,c_11800])).

tff(c_12673,plain,(
    ! [C_1426,B_1427] :
      ( ~ v1_xboole_0(C_1426)
      | v1_xboole_0(k2_zfmisc_1(B_1427,C_1426)) ) ),
    inference(resolution,[status(thm)],[c_12528,c_2])).

tff(c_12902,plain,(
    ! [B_1441,C_1442] :
      ( k2_zfmisc_1(B_1441,C_1442) = '#skF_8'
      | ~ v1_xboole_0(C_1442) ) ),
    inference(resolution,[status(thm)],[c_12673,c_12521])).

tff(c_12971,plain,(
    ! [B_1447] : k2_zfmisc_1(B_1447,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_12520,c_12902])).

tff(c_12999,plain,(
    ! [B_1447,C_27] : k3_zfmisc_1(B_1447,'#skF_8',C_27) = k2_zfmisc_1('#skF_8',C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_12971,c_34])).

tff(c_13020,plain,(
    ! [B_1447,C_27] : k3_zfmisc_1(B_1447,'#skF_8',C_27) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12854,c_12999])).

tff(c_70,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_13025,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13020,c_70])).

tff(c_13031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12520,c_13025])).

tff(c_13032,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12500])).

tff(c_12144,plain,(
    ! [B_1372] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1372)
      | ~ r1_tarski('#skF_9',B_1372) ) ),
    inference(resolution,[status(thm)],[c_12128,c_6])).

tff(c_12221,plain,(
    ! [B_1387,B_1388] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1387)
      | ~ r1_tarski(B_1388,B_1387)
      | ~ r1_tarski('#skF_9',B_1388) ) ),
    inference(resolution,[status(thm)],[c_12144,c_6])).

tff(c_12227,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_6')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_12221])).

tff(c_12236,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12227])).

tff(c_12247,plain,(
    ! [B_6] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_6)
      | ~ r1_tarski('#skF_6',B_6) ) ),
    inference(resolution,[status(thm)],[c_12236,c_6])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),B_11)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12303,plain,(
    ! [A_1392,B_1393,B_1394] :
      ( r2_hidden('#skF_3'(A_1392,B_1393),B_1394)
      | ~ r1_tarski(B_1393,B_1394)
      | r1_xboole_0(A_1392,B_1393) ) ),
    inference(resolution,[status(thm)],[c_14,c_11708])).

tff(c_12328,plain,(
    ! [B_1395,B_1396,A_1397] :
      ( ~ v1_xboole_0(B_1395)
      | ~ r1_tarski(B_1396,B_1395)
      | r1_xboole_0(A_1397,B_1396) ) ),
    inference(resolution,[status(thm)],[c_12303,c_2])).

tff(c_12343,plain,(
    ! [A_17,A_1397] :
      ( ~ v1_xboole_0(A_17)
      | r1_xboole_0(A_1397,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_12328])).

tff(c_12344,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_12343])).

tff(c_12353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12344,c_12039])).

tff(c_12362,plain,(
    ! [A_1400] : r1_xboole_0(A_1400,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_12343])).

tff(c_12369,plain,(
    ! [C_1401,A_1402] :
      ( ~ r2_hidden(C_1401,k1_xboole_0)
      | ~ r2_hidden(C_1401,A_1402) ) ),
    inference(resolution,[status(thm)],[c_12362,c_12])).

tff(c_12398,plain,(
    ! [A_1402] :
      ( ~ r2_hidden(k2_mcart_1('#skF_10'),A_1402)
      | ~ r1_tarski('#skF_6',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12247,c_12369])).

tff(c_12409,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_12398])).

tff(c_13042,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13032,c_12409])).

tff(c_13056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_13042])).

tff(c_13058,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_12398])).

tff(c_12264,plain,(
    ! [B_1390] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1390)
      | ~ r1_tarski('#skF_6',B_1390) ) ),
    inference(resolution,[status(thm)],[c_12236,c_6])).

tff(c_12291,plain,(
    ! [B_1390] :
      ( ~ v1_xboole_0(B_1390)
      | ~ r1_tarski('#skF_6',B_1390) ) ),
    inference(resolution,[status(thm)],[c_12264,c_2])).

tff(c_13063,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_13058,c_12291])).

tff(c_13083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12039,c_13063])).

tff(c_13084,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10394])).

tff(c_13089,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13084,c_48])).

tff(c_13183,plain,(
    ! [A_1464,B_1465,C_1466] : k2_zfmisc_1(k2_zfmisc_1(A_1464,B_1465),C_1466) = k3_zfmisc_1(A_1464,B_1465,C_1466) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_13426,plain,(
    ! [A_1500,C_1501,A_1502,B_1503] :
      ( r2_hidden(k2_mcart_1(A_1500),C_1501)
      | ~ r2_hidden(A_1500,k3_zfmisc_1(A_1502,B_1503,C_1501)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13183,c_36])).

tff(c_13445,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_13089,c_13426])).

tff(c_13086,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13084,c_10381])).

tff(c_13532,plain,(
    ! [A_1514,B_1515,C_1516,D_1517] :
      ( k7_mcart_1(A_1514,B_1515,C_1516,D_1517) = k2_mcart_1(D_1517)
      | ~ m1_subset_1(D_1517,k3_zfmisc_1(A_1514,B_1515,C_1516))
      | k1_xboole_0 = C_1516
      | k1_xboole_0 = B_1515
      | k1_xboole_0 = A_1514 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_13536,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_11688,c_13532])).

tff(c_13574,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13536])).

tff(c_13097,plain,(
    ! [C_1451,B_1452,A_1453] :
      ( r2_hidden(C_1451,B_1452)
      | ~ r2_hidden(C_1451,A_1453)
      | ~ r1_tarski(A_1453,B_1452) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13245,plain,(
    ! [A_1474,B_1475] :
      ( r2_hidden('#skF_1'(A_1474),B_1475)
      | ~ r1_tarski(A_1474,B_1475)
      | v1_xboole_0(A_1474) ) ),
    inference(resolution,[status(thm)],[c_4,c_13097])).

tff(c_13266,plain,(
    ! [B_1476,A_1477] :
      ( ~ v1_xboole_0(B_1476)
      | ~ r1_tarski(A_1477,B_1476)
      | v1_xboole_0(A_1477) ) ),
    inference(resolution,[status(thm)],[c_13245,c_2])).

tff(c_13282,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_13266])).

tff(c_13283,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_13282])).

tff(c_13306,plain,(
    ! [A_1480,B_1481,C_1482] :
      ( ~ r1_xboole_0(A_1480,B_1481)
      | ~ r1_tarski(C_1482,B_1481)
      | ~ r1_tarski(C_1482,A_1480) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13283,c_26])).

tff(c_13393,plain,(
    ! [C_1494,B_1495,A_1496] :
      ( ~ r1_tarski(C_1494,B_1495)
      | ~ r1_tarski(C_1494,k4_xboole_0(A_1496,B_1495)) ) ),
    inference(resolution,[status(thm)],[c_28,c_13306])).

tff(c_13401,plain,(
    ! [B_1495] : ~ r1_tarski(k1_xboole_0,B_1495) ),
    inference(resolution,[status(thm)],[c_24,c_13393])).

tff(c_13406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_13401])).

tff(c_13407,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_13282])).

tff(c_13576,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13574,c_13407])).

tff(c_13581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13086,c_13576])).

tff(c_13582,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_13536])).

tff(c_13646,plain,(
    k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_13582])).

tff(c_13647,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13646,c_11685])).

tff(c_13650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13445,c_13647])).

tff(c_13651,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_13582])).

tff(c_13653,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_13651])).

tff(c_13657,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13653,c_13407])).

tff(c_13166,plain,(
    ! [A_1461,C_1462,B_1463] :
      ( r2_hidden(k2_mcart_1(A_1461),C_1462)
      | ~ r2_hidden(A_1461,k2_zfmisc_1(B_1463,C_1462)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13727,plain,(
    ! [B_1542,C_1543] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1542,C_1543))),C_1543)
      | v1_xboole_0(k2_zfmisc_1(B_1542,C_1543)) ) ),
    inference(resolution,[status(thm)],[c_4,c_13166])).

tff(c_13760,plain,(
    ! [C_1544,B_1545] :
      ( ~ v1_xboole_0(C_1544)
      | v1_xboole_0(k2_zfmisc_1(B_1545,C_1544)) ) ),
    inference(resolution,[status(thm)],[c_13727,c_2])).

tff(c_13658,plain,(
    ! [A_1111] :
      ( A_1111 = '#skF_8'
      | ~ v1_xboole_0(A_1111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13653,c_10438])).

tff(c_13771,plain,(
    ! [B_1546,C_1547] :
      ( k2_zfmisc_1(B_1546,C_1547) = '#skF_8'
      | ~ v1_xboole_0(C_1547) ) ),
    inference(resolution,[status(thm)],[c_13760,c_13658])).

tff(c_13806,plain,(
    ! [B_1549] : k2_zfmisc_1(B_1549,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_13657,c_13771])).

tff(c_13927,plain,(
    ! [A_1562,B_1563] :
      ( r2_hidden(k1_mcart_1(A_1562),B_1563)
      | ~ r2_hidden(A_1562,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13806,c_38])).

tff(c_13951,plain,(
    ! [B_1563,A_1562] :
      ( ~ v1_xboole_0(B_1563)
      | ~ r2_hidden(A_1562,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_13927,c_2])).

tff(c_13952,plain,(
    ! [A_1562] : ~ r2_hidden(A_1562,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_13951])).

tff(c_13821,plain,(
    ! [B_1549,C_27] : k3_zfmisc_1(B_1549,'#skF_8',C_27) = k2_zfmisc_1('#skF_8',C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_13806,c_34])).

tff(c_14107,plain,(
    r2_hidden('#skF_10',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13821,c_13089])).

tff(c_14147,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_14107,c_38])).

tff(c_14158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13952,c_14147])).

tff(c_14159,plain,(
    ! [B_1563] : ~ v1_xboole_0(B_1563) ),
    inference(splitRight,[status(thm)],[c_13951])).

tff(c_14171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14159,c_13657])).

tff(c_14172,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_13651])).

tff(c_14177,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14172,c_13407])).

tff(c_14182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10437,c_14177])).

tff(c_14183,plain,(
    '#skF_6' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_10396])).

tff(c_14199,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_5','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14183,c_50])).

tff(c_14757,plain,(
    ! [A_1665,B_1666,C_1667,D_1668] :
      ( k7_mcart_1(A_1665,B_1666,C_1667,D_1668) = k2_mcart_1(D_1668)
      | ~ m1_subset_1(D_1668,k3_zfmisc_1(A_1665,B_1666,C_1667))
      | k1_xboole_0 = C_1667
      | k1_xboole_0 = B_1666
      | k1_xboole_0 = A_1665 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_14761,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14199,c_14757])).

tff(c_14768,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14761])).

tff(c_14770,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14768,c_14563])).

tff(c_14775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14237,c_14770])).

tff(c_14776,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_9'
    | k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_14761])).

tff(c_14949,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_14776])).

tff(c_14196,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14183,c_10382])).

tff(c_14950,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14949,c_14196])).

tff(c_14953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14594,c_14950])).

tff(c_14954,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_14776])).

tff(c_14956,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_14954])).

tff(c_14966,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14956,c_14563])).

tff(c_14971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14226,c_14966])).

tff(c_14972,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_14954])).

tff(c_14603,plain,(
    ! [B_1644] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1644)
      | ~ r1_tarski('#skF_9',B_1644) ) ),
    inference(resolution,[status(thm)],[c_14594,c_6])).

tff(c_14736,plain,(
    ! [B_1663,B_1664] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1663)
      | ~ r1_tarski(B_1664,B_1663)
      | ~ r1_tarski('#skF_9',B_1664) ) ),
    inference(resolution,[status(thm)],[c_14603,c_6])).

tff(c_14751,plain,(
    ! [A_17] :
      ( r2_hidden(k2_mcart_1('#skF_10'),A_17)
      | ~ r1_tarski('#skF_9',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_14736])).

tff(c_14767,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_14751])).

tff(c_14981,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14972,c_14767])).

tff(c_14990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14981])).

tff(c_14992,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_14751])).

tff(c_14627,plain,(
    ! [B_1644] :
      ( ~ v1_xboole_0(B_1644)
      | ~ r1_tarski('#skF_9',B_1644) ) ),
    inference(resolution,[status(thm)],[c_14603,c_2])).

tff(c_15002,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14992,c_14627])).

tff(c_15020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14563,c_15002])).

tff(c_15021,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10394])).

tff(c_15026,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15021,c_48])).

tff(c_15163,plain,(
    ! [A_1719,C_1720,B_1721] :
      ( r2_hidden(k2_mcart_1(A_1719),C_1720)
      | ~ r2_hidden(A_1719,k2_zfmisc_1(B_1721,C_1720)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_15395,plain,(
    ! [A_1750,C_1751,A_1752,B_1753] :
      ( r2_hidden(k2_mcart_1(A_1750),C_1751)
      | ~ r2_hidden(A_1750,k3_zfmisc_1(A_1752,B_1753,C_1751)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_15163])).

tff(c_15418,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_15026,c_15395])).

tff(c_15429,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_15418,c_2])).

tff(c_15023,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15021,c_10381])).

tff(c_15430,plain,(
    ! [A_1754,B_1755,C_1756,D_1757] :
      ( k7_mcart_1(A_1754,B_1755,C_1756,D_1757) = k2_mcart_1(D_1757)
      | ~ m1_subset_1(D_1757,k3_zfmisc_1(A_1754,B_1755,C_1756))
      | k1_xboole_0 = C_1756
      | k1_xboole_0 = B_1755
      | k1_xboole_0 = A_1754 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_15434,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14199,c_15430])).

tff(c_15478,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_15434])).

tff(c_15084,plain,(
    ! [C_1706,B_1707,A_1708] :
      ( r2_hidden(C_1706,B_1707)
      | ~ r2_hidden(C_1706,A_1708)
      | ~ r1_tarski(A_1708,B_1707) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_15182,plain,(
    ! [A_1722,B_1723] :
      ( r2_hidden('#skF_1'(A_1722),B_1723)
      | ~ r1_tarski(A_1722,B_1723)
      | v1_xboole_0(A_1722) ) ),
    inference(resolution,[status(thm)],[c_4,c_15084])).

tff(c_15213,plain,(
    ! [B_1727,A_1728] :
      ( ~ v1_xboole_0(B_1727)
      | ~ r1_tarski(A_1728,B_1727)
      | v1_xboole_0(A_1728) ) ),
    inference(resolution,[status(thm)],[c_15182,c_2])).

tff(c_15229,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_15213])).

tff(c_15230,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_15229])).

tff(c_15314,plain,(
    ! [A_1740,B_1741,C_1742] :
      ( ~ r1_xboole_0(A_1740,B_1741)
      | ~ r1_tarski(C_1742,B_1741)
      | ~ r1_tarski(C_1742,A_1740) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15230,c_26])).

tff(c_15340,plain,(
    ! [C_1745,B_1746,A_1747] :
      ( ~ r1_tarski(C_1745,B_1746)
      | ~ r1_tarski(C_1745,k4_xboole_0(A_1747,B_1746)) ) ),
    inference(resolution,[status(thm)],[c_28,c_15314])).

tff(c_15348,plain,(
    ! [B_1746] : ~ r1_tarski(k1_xboole_0,B_1746) ),
    inference(resolution,[status(thm)],[c_24,c_15340])).

tff(c_15353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_15348])).

tff(c_15354,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_15229])).

tff(c_15480,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15478,c_15354])).

tff(c_15485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15023,c_15480])).

tff(c_15486,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_9'
    | k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_15434])).

tff(c_15535,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_15486])).

tff(c_15536,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15535,c_14196])).

tff(c_15539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15418,c_15536])).

tff(c_15540,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_15486])).

tff(c_15542,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_15540])).

tff(c_15546,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15542,c_15354])).

tff(c_15551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14226,c_15546])).

tff(c_15552,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_15540])).

tff(c_15558,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15552,c_15354])).

tff(c_15563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15429,c_15558])).

tff(c_15564,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_10395])).

tff(c_15571,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15564,c_14199])).

tff(c_15949,plain,(
    ! [A_1836,B_1837,C_1838,D_1839] :
      ( k7_mcart_1(A_1836,B_1837,C_1838,D_1839) = k2_mcart_1(D_1839)
      | ~ m1_subset_1(D_1839,k3_zfmisc_1(A_1836,B_1837,C_1838))
      | k1_xboole_0 = C_1838
      | k1_xboole_0 = B_1837
      | k1_xboole_0 = A_1836 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_15953,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15571,c_15949])).

tff(c_16300,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_15953])).

tff(c_16310,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16300,c_15916])).

tff(c_16315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15589,c_16310])).

tff(c_16317,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15953])).

tff(c_16038,plain,(
    ! [A_1852,B_1853,C_1854,D_1855] :
      ( k6_mcart_1(A_1852,B_1853,C_1854,D_1855) = k2_mcart_1(k1_mcart_1(D_1855))
      | ~ m1_subset_1(D_1855,k3_zfmisc_1(A_1852,B_1853,C_1854))
      | k1_xboole_0 = C_1854
      | k1_xboole_0 = B_1853
      | k1_xboole_0 = A_1852 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16042,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15571,c_16038])).

tff(c_16440,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_16317,c_16042])).

tff(c_16441,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_16440])).

tff(c_16457,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16441,c_15916])).

tff(c_15700,plain,(
    ! [A_1799,B_1800,C_1801] :
      ( r2_hidden(k1_mcart_1(A_1799),B_1800)
      | ~ r2_hidden(A_1799,k2_zfmisc_1(B_1800,C_1801)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16136,plain,(
    ! [B_1873,C_1874] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1873,C_1874))),B_1873)
      | v1_xboole_0(k2_zfmisc_1(B_1873,C_1874)) ) ),
    inference(resolution,[status(thm)],[c_4,c_15700])).

tff(c_16167,plain,(
    ! [B_1875,C_1876] :
      ( ~ v1_xboole_0(B_1875)
      | v1_xboole_0(k2_zfmisc_1(B_1875,C_1876)) ) ),
    inference(resolution,[status(thm)],[c_16136,c_2])).

tff(c_14212,plain,(
    ! [A_1582,B_1583] :
      ( ~ v1_xboole_0(A_1582)
      | r1_tarski(A_1582,B_1583) ) ),
    inference(resolution,[status(thm)],[c_14185,c_2])).

tff(c_14219,plain,(
    ! [A_1582] :
      ( k1_xboole_0 = A_1582
      | ~ v1_xboole_0(A_1582) ) ),
    inference(resolution,[status(thm)],[c_14212,c_10401])).

tff(c_16178,plain,(
    ! [B_1877,C_1878] :
      ( k2_zfmisc_1(B_1877,C_1878) = k1_xboole_0
      | ~ v1_xboole_0(B_1877) ) ),
    inference(resolution,[status(thm)],[c_16167,c_14219])).

tff(c_16185,plain,(
    ! [C_1878] : k2_zfmisc_1(k1_xboole_0,C_1878) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15916,c_16178])).

tff(c_16451,plain,(
    ! [C_1878] : k2_zfmisc_1('#skF_8',C_1878) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16441,c_16441,c_16185])).

tff(c_16615,plain,(
    ! [B_1907,C_1908] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1907,C_1908))),C_1908)
      | v1_xboole_0(k2_zfmisc_1(B_1907,C_1908)) ) ),
    inference(resolution,[status(thm)],[c_4,c_15650])).

tff(c_16186,plain,(
    ! [C_1879] : k2_zfmisc_1(k1_xboole_0,C_1879) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15916,c_16178])).

tff(c_16270,plain,(
    ! [A_1888,C_1889] :
      ( r2_hidden(k2_mcart_1(A_1888),C_1889)
      | ~ r2_hidden(A_1888,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16186,c_36])).

tff(c_16298,plain,(
    ! [C_1889,A_1888] :
      ( ~ v1_xboole_0(C_1889)
      | ~ r2_hidden(A_1888,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16270,c_2])).

tff(c_16299,plain,(
    ! [A_1888] : ~ r2_hidden(A_1888,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_16298])).

tff(c_16447,plain,(
    ! [A_1888] : ~ r2_hidden(A_1888,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16441,c_16299])).

tff(c_16685,plain,(
    ! [B_1910] : v1_xboole_0(k2_zfmisc_1(B_1910,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_16615,c_16447])).

tff(c_16458,plain,(
    ! [A_1582] :
      ( A_1582 = '#skF_8'
      | ~ v1_xboole_0(A_1582) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16441,c_14219])).

tff(c_16703,plain,(
    ! [B_1911] : k2_zfmisc_1(B_1911,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_16685,c_16458])).

tff(c_16728,plain,(
    ! [B_1911,C_27] : k3_zfmisc_1(B_1911,'#skF_8',C_27) = k2_zfmisc_1('#skF_8',C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_16703,c_34])).

tff(c_16750,plain,(
    ! [B_1911,C_27] : k3_zfmisc_1(B_1911,'#skF_8',C_27) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16451,c_16728])).

tff(c_16878,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16750,c_70])).

tff(c_16884,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16457,c_16878])).

tff(c_16886,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_16440])).

tff(c_16097,plain,(
    ! [A_1861,B_1862,C_1863,D_1864] :
      ( k5_mcart_1(A_1861,B_1862,C_1863,D_1864) = k1_mcart_1(k1_mcart_1(D_1864))
      | ~ m1_subset_1(D_1864,k3_zfmisc_1(A_1861,B_1862,C_1863))
      | k1_xboole_0 = C_1863
      | k1_xboole_0 = B_1862
      | k1_xboole_0 = A_1861 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16101,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15571,c_16097])).

tff(c_16944,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_16317,c_16886,c_16101])).

tff(c_16945,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_16944])).

tff(c_15961,plain,(
    ! [B_1840] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1840)
      | ~ r1_tarski('#skF_9',B_1840) ) ),
    inference(resolution,[status(thm)],[c_15947,c_6])).

tff(c_16049,plain,(
    ! [B_1858,B_1859] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1858)
      | ~ r1_tarski(B_1859,B_1858)
      | ~ r1_tarski('#skF_9',B_1859) ) ),
    inference(resolution,[status(thm)],[c_15961,c_6])).

tff(c_16061,plain,(
    ! [A_17] :
      ( r2_hidden(k2_mcart_1('#skF_10'),A_17)
      | ~ r1_tarski('#skF_9',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_16049])).

tff(c_16067,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_16061])).

tff(c_16961,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16945,c_16067])).

tff(c_16970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16961])).

tff(c_16972,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_16944])).

tff(c_16316,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9'
    | k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_15953])).

tff(c_17274,plain,(
    k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_16972,c_16886,c_16316])).

tff(c_15630,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15564,c_14196])).

tff(c_17275,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17274,c_15630])).

tff(c_17278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15947,c_17275])).

tff(c_17279,plain,(
    ! [C_1889] : ~ v1_xboole_0(C_1889) ),
    inference(splitRight,[status(thm)],[c_16298])).

tff(c_17290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17279,c_15916])).

tff(c_17292,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_16061])).

tff(c_15985,plain,(
    ! [B_1840] :
      ( ~ v1_xboole_0(B_1840)
      | ~ r1_tarski('#skF_9',B_1840) ) ),
    inference(resolution,[status(thm)],[c_15961,c_2])).

tff(c_17297,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_17292,c_15985])).

tff(c_17315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15916,c_17297])).

tff(c_17316,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10394])).

tff(c_17321,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17316,c_48])).

tff(c_17425,plain,(
    ! [A_1967,C_1968,B_1969] :
      ( r2_hidden(k2_mcart_1(A_1967),C_1968)
      | ~ r2_hidden(A_1967,k2_zfmisc_1(B_1969,C_1968)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_17664,plain,(
    ! [A_2003,C_2004,A_2005,B_2006] :
      ( r2_hidden(k2_mcart_1(A_2003),C_2004)
      | ~ r2_hidden(A_2003,k3_zfmisc_1(A_2005,B_2006,C_2004)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_17425])).

tff(c_17683,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_17321,c_17664])).

tff(c_17318,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17316,c_10381])).

tff(c_17839,plain,(
    ! [A_2028,B_2029,C_2030,D_2031] :
      ( k7_mcart_1(A_2028,B_2029,C_2030,D_2031) = k2_mcart_1(D_2031)
      | ~ m1_subset_1(D_2031,k3_zfmisc_1(A_2028,B_2029,C_2030))
      | k1_xboole_0 = C_2030
      | k1_xboole_0 = B_2029
      | k1_xboole_0 = A_2028 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_17843,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15571,c_17839])).

tff(c_17883,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_17843])).

tff(c_17886,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17883,c_17655])).

tff(c_17891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17318,c_17886])).

tff(c_17892,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9'
    | k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_17843])).

tff(c_17982,plain,(
    k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_17892])).

tff(c_17369,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_4','#skF_8','#skF_9','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15564,c_14196])).

tff(c_17983,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17982,c_17369])).

tff(c_17986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17683,c_17983])).

tff(c_17987,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_17892])).

tff(c_17989,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_17987])).

tff(c_17997,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17989,c_17655])).

tff(c_17456,plain,(
    ! [A_1971,B_1972,C_1973] :
      ( r2_hidden(k1_mcart_1(A_1971),B_1972)
      | ~ r2_hidden(A_1971,k2_zfmisc_1(B_1972,C_1973)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18178,plain,(
    ! [B_2071,C_2072] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2071,C_2072))),B_2071)
      | v1_xboole_0(k2_zfmisc_1(B_2071,C_2072)) ) ),
    inference(resolution,[status(thm)],[c_4,c_17456])).

tff(c_18213,plain,(
    ! [B_2073,C_2074] :
      ( ~ v1_xboole_0(B_2073)
      | v1_xboole_0(k2_zfmisc_1(B_2073,C_2074)) ) ),
    inference(resolution,[status(thm)],[c_18178,c_2])).

tff(c_17998,plain,(
    ! [A_1582] :
      ( A_1582 = '#skF_8'
      | ~ v1_xboole_0(A_1582) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17989,c_14219])).

tff(c_18224,plain,(
    ! [B_2075,C_2076] :
      ( k2_zfmisc_1(B_2075,C_2076) = '#skF_8'
      | ~ v1_xboole_0(B_2075) ) ),
    inference(resolution,[status(thm)],[c_18213,c_17998])).

tff(c_18232,plain,(
    ! [C_2077] : k2_zfmisc_1('#skF_8',C_2077) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_17997,c_18224])).

tff(c_18289,plain,(
    ! [A_2083] :
      ( r2_hidden(k1_mcart_1(A_2083),'#skF_8')
      | ~ r2_hidden(A_2083,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18232,c_38])).

tff(c_18296,plain,(
    ! [A_2083] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ r2_hidden(A_2083,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18289,c_2])).

tff(c_18303,plain,(
    ! [A_2083] : ~ r2_hidden(A_2083,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17997,c_18296])).

tff(c_18231,plain,(
    ! [C_2076] : k2_zfmisc_1('#skF_8',C_2076) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_17997,c_18224])).

tff(c_18443,plain,(
    ! [B_2095,C_2096] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2095,C_2096))),C_2096)
      | v1_xboole_0(k2_zfmisc_1(B_2095,C_2096)) ) ),
    inference(resolution,[status(thm)],[c_4,c_17425])).

tff(c_18481,plain,(
    ! [B_2097] : v1_xboole_0(k2_zfmisc_1(B_2097,'#skF_8')) ),
    inference(resolution,[status(thm)],[c_18443,c_18303])).

tff(c_18505,plain,(
    ! [B_2098] : k2_zfmisc_1(B_2098,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_18481,c_17998])).

tff(c_18530,plain,(
    ! [B_2098,C_27] : k3_zfmisc_1(B_2098,'#skF_8',C_27) = k2_zfmisc_1('#skF_8',C_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_18505,c_34])).

tff(c_18552,plain,(
    ! [B_2098,C_27] : k3_zfmisc_1(B_2098,'#skF_8',C_27) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18231,c_18530])).

tff(c_18604,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18552,c_17321])).

tff(c_18609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18303,c_18604])).

tff(c_18610,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_17987])).

tff(c_17695,plain,(
    ! [B_2007] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2007)
      | ~ r1_tarski('#skF_9',B_2007) ) ),
    inference(resolution,[status(thm)],[c_17683,c_6])).

tff(c_17824,plain,(
    ! [B_2026,B_2027] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2026)
      | ~ r1_tarski(B_2027,B_2026)
      | ~ r1_tarski('#skF_9',B_2027) ) ),
    inference(resolution,[status(thm)],[c_17695,c_6])).

tff(c_17833,plain,(
    ! [A_17] :
      ( r2_hidden(k2_mcart_1('#skF_10'),A_17)
      | ~ r1_tarski('#skF_9',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_17824])).

tff(c_17834,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_17833])).

tff(c_18618,plain,(
    ~ r1_tarski('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18610,c_17834])).

tff(c_18625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18618])).

tff(c_18627,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_17833])).

tff(c_17719,plain,(
    ! [B_2007] :
      ( ~ v1_xboole_0(B_2007)
      | ~ r1_tarski('#skF_9',B_2007) ) ),
    inference(resolution,[status(thm)],[c_17695,c_2])).

tff(c_18637,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18627,c_17719])).

tff(c_18655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17655,c_18637])).

tff(c_18656,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_10376])).

tff(c_18668,plain,(
    ! [A_2111,B_2112] :
      ( r2_hidden('#skF_2'(A_2111,B_2112),A_2111)
      | r1_tarski(A_2111,B_2112) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18678,plain,(
    ! [A_2111,B_2112] :
      ( ~ v1_xboole_0(A_2111)
      | r1_tarski(A_2111,B_2112) ) ),
    inference(resolution,[status(thm)],[c_18668,c_2])).

tff(c_18680,plain,(
    ! [B_2115,A_2116] :
      ( B_2115 = A_2116
      | ~ r1_tarski(B_2115,A_2116)
      | ~ r1_tarski(A_2116,B_2115) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18695,plain,
    ( '#skF_5' = '#skF_8'
    | ~ r1_tarski('#skF_5','#skF_8') ),
    inference(resolution,[status(thm)],[c_87,c_18680])).

tff(c_18721,plain,(
    ~ r1_tarski('#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_18695])).

tff(c_20319,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_18678,c_18721])).

tff(c_18777,plain,(
    ! [C_2124,B_2125,A_2126] :
      ( r2_hidden(C_2124,B_2125)
      | ~ r2_hidden(C_2124,A_2126)
      | ~ r1_tarski(A_2126,B_2125) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18891,plain,(
    ! [A_2145,B_2146] :
      ( r2_hidden('#skF_1'(A_2145),B_2146)
      | ~ r1_tarski(A_2145,B_2146)
      | v1_xboole_0(A_2145) ) ),
    inference(resolution,[status(thm)],[c_4,c_18777])).

tff(c_18912,plain,(
    ! [B_2147,A_2148] :
      ( ~ v1_xboole_0(B_2147)
      | ~ r1_tarski(A_2148,B_2147)
      | v1_xboole_0(A_2148) ) ),
    inference(resolution,[status(thm)],[c_18891,c_2])).

tff(c_18938,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_18912])).

tff(c_18960,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_18938])).

tff(c_18984,plain,(
    ! [A_2154,B_2155,C_2156] :
      ( ~ r1_xboole_0(A_2154,B_2155)
      | ~ r1_tarski(C_2156,B_2155)
      | ~ r1_tarski(C_2156,A_2154) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18960,c_26])).

tff(c_19070,plain,(
    ! [C_2166,B_2167,A_2168] :
      ( ~ r1_tarski(C_2166,B_2167)
      | ~ r1_tarski(C_2166,k4_xboole_0(A_2168,B_2167)) ) ),
    inference(resolution,[status(thm)],[c_28,c_18984])).

tff(c_19078,plain,(
    ! [B_2167] : ~ r1_tarski(k1_xboole_0,B_2167) ),
    inference(resolution,[status(thm)],[c_24,c_19070])).

tff(c_19083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_19078])).

tff(c_19084,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_18938])).

tff(c_18726,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_18678,c_18721])).

tff(c_18694,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_88,c_18680])).

tff(c_18722,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_18694])).

tff(c_18730,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18678,c_18722])).

tff(c_19108,plain,(
    ! [A_2170,B_2171,C_2172,D_2173] :
      ( k7_mcart_1(A_2170,B_2171,C_2172,D_2173) = k2_mcart_1(D_2173)
      | ~ m1_subset_1(D_2173,k3_zfmisc_1(A_2170,B_2171,C_2172))
      | k1_xboole_0 = C_2172
      | k1_xboole_0 = B_2171
      | k1_xboole_0 = A_2170 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_19112,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_19108])).

tff(c_19158,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_19112])).

tff(c_19160,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19158,c_19084])).

tff(c_19165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18730,c_19160])).

tff(c_19167,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_19112])).

tff(c_19285,plain,(
    ! [A_2197,B_2198,C_2199,D_2200] :
      ( k6_mcart_1(A_2197,B_2198,C_2199,D_2200) = k2_mcart_1(k1_mcart_1(D_2200))
      | ~ m1_subset_1(D_2200,k3_zfmisc_1(A_2197,B_2198,C_2199))
      | k1_xboole_0 = C_2199
      | k1_xboole_0 = B_2198
      | k1_xboole_0 = A_2197 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_19288,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_19285])).

tff(c_19291,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_19167,c_19288])).

tff(c_19414,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_19291])).

tff(c_19420,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19414,c_19084])).

tff(c_19425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18726,c_19420])).

tff(c_19426,plain,
    ( k1_xboole_0 = '#skF_6'
    | k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_19291])).

tff(c_19458,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_19426])).

tff(c_18850,plain,(
    ! [A_2138,B_2139,C_2140] :
      ( r2_hidden(k1_mcart_1(A_2138),B_2139)
      | ~ r2_hidden(A_2138,k2_zfmisc_1(B_2139,C_2140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20180,plain,(
    ! [A_2276,A_2277,B_2278,C_2279] :
      ( r2_hidden(k1_mcart_1(A_2276),k2_zfmisc_1(A_2277,B_2278))
      | ~ r2_hidden(A_2276,k3_zfmisc_1(A_2277,B_2278,C_2279)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_18850])).

tff(c_20244,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_20180])).

tff(c_20249,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_20244,c_36])).

tff(c_20258,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19458,c_20249])).

tff(c_20260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18656,c_20258])).

tff(c_20261,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_19426])).

tff(c_18831,plain,(
    ! [A_2135,C_2136,B_2137] :
      ( r2_hidden(k2_mcart_1(A_2135),C_2136)
      | ~ r2_hidden(A_2135,k2_zfmisc_1(B_2137,C_2136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_19183,plain,(
    ! [A_2181,C_2182,A_2183,B_2184] :
      ( r2_hidden(k2_mcart_1(A_2181),C_2182)
      | ~ r2_hidden(A_2181,k3_zfmisc_1(A_2183,B_2184,C_2182)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_18831])).

tff(c_19213,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_19183])).

tff(c_19229,plain,(
    ! [B_2189] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2189)
      | ~ r1_tarski('#skF_9',B_2189) ) ),
    inference(resolution,[status(thm)],[c_19213,c_6])).

tff(c_19299,plain,(
    ! [B_2203,B_2204] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2203)
      | ~ r1_tarski(B_2204,B_2203)
      | ~ r1_tarski('#skF_9',B_2204) ) ),
    inference(resolution,[status(thm)],[c_19229,c_6])).

tff(c_19319,plain,(
    ! [A_17] :
      ( r2_hidden(k2_mcart_1('#skF_10'),A_17)
      | ~ r1_tarski('#skF_9',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_19299])).

tff(c_19340,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_19319])).

tff(c_20264,plain,(
    ~ r1_tarski('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20261,c_19340])).

tff(c_20275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_20264])).

tff(c_20277,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_19319])).

tff(c_18657,plain,(
    r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_10376])).

tff(c_19137,plain,(
    ! [B_2179] :
      ( r2_hidden(k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),B_2179)
      | ~ r1_tarski('#skF_9',B_2179) ) ),
    inference(resolution,[status(thm)],[c_18657,c_18777])).

tff(c_19157,plain,(
    ! [B_2179] :
      ( ~ v1_xboole_0(B_2179)
      | ~ r1_tarski('#skF_9',B_2179) ) ),
    inference(resolution,[status(thm)],[c_19137,c_2])).

tff(c_20282,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20277,c_19157])).

tff(c_20300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19084,c_20282])).

tff(c_20301,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18694])).

tff(c_20304,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20301,c_10381])).

tff(c_20891,plain,(
    ! [A_2361,B_2362,C_2363,D_2364] :
      ( k7_mcart_1(A_2361,B_2362,C_2363,D_2364) = k2_mcart_1(D_2364)
      | ~ m1_subset_1(D_2364,k3_zfmisc_1(A_2361,B_2362,C_2363))
      | k1_xboole_0 = C_2363
      | k1_xboole_0 = B_2362
      | k1_xboole_0 = A_2361 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_20895,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_20891])).

tff(c_20912,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_20895])).

tff(c_20914,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20912,c_20661])).

tff(c_20919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20304,c_20914])).

tff(c_20921,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20895])).

tff(c_21018,plain,(
    ! [A_2380,B_2381,C_2382,D_2383] :
      ( k5_mcart_1(A_2380,B_2381,C_2382,D_2383) = k1_mcart_1(k1_mcart_1(D_2383))
      | ~ m1_subset_1(D_2383,k3_zfmisc_1(A_2380,B_2381,C_2382))
      | k1_xboole_0 = C_2382
      | k1_xboole_0 = B_2381
      | k1_xboole_0 = A_2380 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_21021,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_21018])).

tff(c_21024,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_20921,c_21021])).

tff(c_21044,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_21024])).

tff(c_21050,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21044,c_20661])).

tff(c_21055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20319,c_21050])).

tff(c_21057,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_21024])).

tff(c_20931,plain,(
    ! [A_2366,B_2367,C_2368,D_2369] :
      ( k6_mcart_1(A_2366,B_2367,C_2368,D_2369) = k2_mcart_1(k1_mcart_1(D_2369))
      | ~ m1_subset_1(D_2369,k3_zfmisc_1(A_2366,B_2367,C_2368))
      | k1_xboole_0 = C_2368
      | k1_xboole_0 = B_2367
      | k1_xboole_0 = A_2366 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_20934,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_20931])).

tff(c_20937,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_20921,c_20934])).

tff(c_21328,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_21057,c_20937])).

tff(c_21329,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_21328])).

tff(c_20308,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20301,c_48])).

tff(c_20459,plain,(
    ! [A_2300,C_2301,B_2302] :
      ( r2_hidden(k2_mcart_1(A_2300),C_2301)
      | ~ r2_hidden(A_2300,k2_zfmisc_1(B_2302,C_2301)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20670,plain,(
    ! [A_2331,C_2332,A_2333,B_2334] :
      ( r2_hidden(k2_mcart_1(A_2331),C_2332)
      | ~ r2_hidden(A_2331,k3_zfmisc_1(A_2333,B_2334,C_2332)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_20459])).

tff(c_20689,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_20308,c_20670])).

tff(c_20701,plain,(
    ! [B_2335] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2335)
      | ~ r1_tarski('#skF_9',B_2335) ) ),
    inference(resolution,[status(thm)],[c_20689,c_6])).

tff(c_20873,plain,(
    ! [B_2359,B_2360] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2359)
      | ~ r1_tarski(B_2360,B_2359)
      | ~ r1_tarski('#skF_9',B_2360) ) ),
    inference(resolution,[status(thm)],[c_20701,c_6])).

tff(c_20890,plain,(
    ! [A_17] :
      ( r2_hidden(k2_mcart_1('#skF_10'),A_17)
      | ~ r1_tarski('#skF_9',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_20873])).

tff(c_20911,plain,(
    ~ r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_20890])).

tff(c_21340,plain,(
    ~ r1_tarski('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21329,c_20911])).

tff(c_21349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_21340])).

tff(c_21350,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_21328])).

tff(c_20430,plain,(
    ! [A_2296,B_2297,C_2298] : k2_zfmisc_1(k2_zfmisc_1(A_2296,B_2297),C_2298) = k3_zfmisc_1(A_2296,B_2297,C_2298) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22375,plain,(
    ! [A_2492,A_2493,B_2494,C_2495] :
      ( r2_hidden(k1_mcart_1(A_2492),k2_zfmisc_1(A_2493,B_2494))
      | ~ r2_hidden(A_2492,k3_zfmisc_1(A_2493,B_2494,C_2495)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20430,c_38])).

tff(c_22439,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_20308,c_22375])).

tff(c_22445,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_22439,c_36])).

tff(c_22454,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21350,c_22445])).

tff(c_22456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18656,c_22454])).

tff(c_22458,plain,(
    r1_tarski('#skF_9',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_20890])).

tff(c_20725,plain,(
    ! [B_2335] :
      ( ~ v1_xboole_0(B_2335)
      | ~ r1_tarski('#skF_9',B_2335) ) ),
    inference(resolution,[status(thm)],[c_20701,c_2])).

tff(c_22463,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22458,c_20725])).

tff(c_22481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20661,c_22463])).

tff(c_22482,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_18695])).

tff(c_22485,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22482,c_18656])).

tff(c_22559,plain,(
    ! [C_2503,B_2504,A_2505] :
      ( r2_hidden(C_2503,B_2504)
      | ~ r2_hidden(C_2503,A_2505)
      | ~ r1_tarski(A_2505,B_2504) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22660,plain,(
    ! [A_2519,B_2520] :
      ( r2_hidden('#skF_1'(A_2519),B_2520)
      | ~ r1_tarski(A_2519,B_2520)
      | v1_xboole_0(A_2519) ) ),
    inference(resolution,[status(thm)],[c_4,c_22559])).

tff(c_22681,plain,(
    ! [B_2521,A_2522] :
      ( ~ v1_xboole_0(B_2521)
      | ~ r1_tarski(A_2522,B_2521)
      | v1_xboole_0(A_2522) ) ),
    inference(resolution,[status(thm)],[c_22660,c_2])).

tff(c_22703,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_22681])).

tff(c_22704,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_22703])).

tff(c_22727,plain,(
    ! [A_2525,B_2526,C_2527] :
      ( ~ r1_xboole_0(A_2525,B_2526)
      | ~ r1_tarski(C_2527,B_2526)
      | ~ r1_tarski(C_2527,A_2525) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22704,c_26])).

tff(c_22814,plain,(
    ! [C_2539,B_2540,A_2541] :
      ( ~ r1_tarski(C_2539,B_2540)
      | ~ r1_tarski(C_2539,k4_xboole_0(A_2541,B_2540)) ) ),
    inference(resolution,[status(thm)],[c_28,c_22727])).

tff(c_22822,plain,(
    ! [B_2540] : ~ r1_tarski(k1_xboole_0,B_2540) ),
    inference(resolution,[status(thm)],[c_24,c_22814])).

tff(c_22827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22822])).

tff(c_22828,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_22703])).

tff(c_22501,plain,(
    ~ r1_tarski('#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_18694])).

tff(c_22505,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_18678,c_22501])).

tff(c_22488,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22482,c_50])).

tff(c_22959,plain,(
    ! [A_2561,B_2562,C_2563,D_2564] :
      ( k7_mcart_1(A_2561,B_2562,C_2563,D_2564) = k2_mcart_1(D_2564)
      | ~ m1_subset_1(D_2564,k3_zfmisc_1(A_2561,B_2562,C_2563))
      | k1_xboole_0 = C_2563
      | k1_xboole_0 = B_2562
      | k1_xboole_0 = A_2561 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22963,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22488,c_22959])).

tff(c_23020,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22963])).

tff(c_23022,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23020,c_22828])).

tff(c_23027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22505,c_23022])).

tff(c_23029,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22963])).

tff(c_23059,plain,(
    ! [A_2574,B_2575,C_2576,D_2577] :
      ( k5_mcart_1(A_2574,B_2575,C_2576,D_2577) = k1_mcart_1(k1_mcart_1(D_2577))
      | ~ m1_subset_1(D_2577,k3_zfmisc_1(A_2574,B_2575,C_2576))
      | k1_xboole_0 = C_2576
      | k1_xboole_0 = B_2575
      | k1_xboole_0 = A_2574 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_23062,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22488,c_23059])).

tff(c_23065,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_23029,c_23062])).

tff(c_23889,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_23065])).

tff(c_22612,plain,(
    ! [A_2512,C_2513,B_2514] :
      ( r2_hidden(k2_mcart_1(A_2512),C_2513)
      | ~ r2_hidden(A_2512,k2_zfmisc_1(B_2514,C_2513)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_23294,plain,(
    ! [B_2608,C_2609] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2608,C_2609))),C_2609)
      | v1_xboole_0(k2_zfmisc_1(B_2608,C_2609)) ) ),
    inference(resolution,[status(thm)],[c_4,c_22612])).

tff(c_23323,plain,(
    ! [C_2610,B_2611] :
      ( ~ v1_xboole_0(C_2610)
      | v1_xboole_0(k2_zfmisc_1(B_2611,C_2610)) ) ),
    inference(resolution,[status(thm)],[c_23294,c_2])).

tff(c_18702,plain,(
    ! [A_2117] :
      ( k1_xboole_0 = A_2117
      | ~ r1_tarski(A_2117,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_18680])).

tff(c_18715,plain,(
    ! [A_2111] :
      ( k1_xboole_0 = A_2111
      | ~ v1_xboole_0(A_2111) ) ),
    inference(resolution,[status(thm)],[c_18678,c_18702])).

tff(c_23334,plain,(
    ! [B_2612,C_2613] :
      ( k2_zfmisc_1(B_2612,C_2613) = k1_xboole_0
      | ~ v1_xboole_0(C_2613) ) ),
    inference(resolution,[status(thm)],[c_23323,c_18715])).

tff(c_23341,plain,(
    ! [B_2614] : k2_zfmisc_1(B_2614,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22828,c_23334])).

tff(c_23552,plain,(
    ! [A_2633] :
      ( r2_hidden(k2_mcart_1(A_2633),k1_xboole_0)
      | ~ r2_hidden(A_2633,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23341,c_36])).

tff(c_23568,plain,(
    ! [A_2633] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_2633,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_23552,c_2])).

tff(c_23578,plain,(
    ! [A_2633] : ~ r2_hidden(A_2633,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22828,c_23568])).

tff(c_23897,plain,(
    ! [A_2633] : ~ r2_hidden(A_2633,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23889,c_23578])).

tff(c_22629,plain,(
    ! [A_2515,B_2516,C_2517] : k2_zfmisc_1(k2_zfmisc_1(A_2515,B_2516),C_2517) = k3_zfmisc_1(A_2515,B_2516,C_2517) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_23958,plain,(
    ! [A_2655,A_2656,B_2657,C_2658] :
      ( r2_hidden(k1_mcart_1(A_2655),k2_zfmisc_1(A_2656,B_2657))
      | ~ r2_hidden(A_2655,k3_zfmisc_1(A_2656,B_2657,C_2658)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22629,c_38])).

tff(c_24012,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_23958])).

tff(c_24092,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_24012,c_36])).

tff(c_24103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23897,c_24092])).

tff(c_24105,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_23065])).

tff(c_23148,plain,(
    ! [A_2583,B_2584,C_2585,D_2586] :
      ( k6_mcart_1(A_2583,B_2584,C_2585,D_2586) = k2_mcart_1(k1_mcart_1(D_2586))
      | ~ m1_subset_1(D_2586,k3_zfmisc_1(A_2583,B_2584,C_2585))
      | k1_xboole_0 = C_2585
      | k1_xboole_0 = B_2584
      | k1_xboole_0 = A_2583 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_23151,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22488,c_23148])).

tff(c_23154,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_23029,c_23151])).

tff(c_24280,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_24105,c_23154])).

tff(c_24281,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_24280])).

tff(c_22847,plain,(
    ! [A_2545,C_2546,A_2547,B_2548] :
      ( r2_hidden(k2_mcart_1(A_2545),C_2546)
      | ~ r2_hidden(A_2545,k3_zfmisc_1(A_2547,B_2548,C_2546)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22629,c_36])).

tff(c_22869,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_22847])).

tff(c_22878,plain,(
    ! [B_2549] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2549)
      | ~ r1_tarski('#skF_9',B_2549) ) ),
    inference(resolution,[status(thm)],[c_22869,c_6])).

tff(c_23066,plain,(
    ! [B_2578,B_2579] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2578)
      | ~ r1_tarski(B_2579,B_2578)
      | ~ r1_tarski('#skF_9',B_2579) ) ),
    inference(resolution,[status(thm)],[c_22878,c_6])).

tff(c_23072,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_6')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_23066])).

tff(c_23081,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_23072])).

tff(c_23109,plain,(
    ! [B_2581] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2581)
      | ~ r1_tarski('#skF_6',B_2581) ) ),
    inference(resolution,[status(thm)],[c_23081,c_6])).

tff(c_23200,plain,(
    ! [B_2599,B_2600] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2599)
      | ~ r1_tarski(B_2600,B_2599)
      | ~ r1_tarski('#skF_6',B_2600) ) ),
    inference(resolution,[status(thm)],[c_23109,c_6])).

tff(c_23216,plain,(
    ! [A_17] :
      ( r2_hidden(k2_mcart_1('#skF_10'),A_17)
      | ~ r1_tarski('#skF_6',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_23200])).

tff(c_23247,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_23216])).

tff(c_24301,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24281,c_23247])).

tff(c_24313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24301])).

tff(c_24314,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_24280])).

tff(c_24557,plain,(
    ! [A_2694,A_2695,B_2696,C_2697] :
      ( r2_hidden(k1_mcart_1(A_2694),k2_zfmisc_1(A_2695,B_2696))
      | ~ r2_hidden(A_2694,k3_zfmisc_1(A_2695,B_2696,C_2697)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22629,c_38])).

tff(c_24624,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_48,c_24557])).

tff(c_24627,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_24624,c_36])).

tff(c_24636,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24314,c_24627])).

tff(c_24638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22485,c_24636])).

tff(c_24640,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_23216])).

tff(c_23136,plain,(
    ! [B_2581] :
      ( ~ v1_xboole_0(B_2581)
      | ~ r1_tarski('#skF_6',B_2581) ) ),
    inference(resolution,[status(thm)],[c_23109,c_2])).

tff(c_24645,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24640,c_23136])).

tff(c_24665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22828,c_24645])).

tff(c_24666,plain,(
    '#skF_7' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18694])).

tff(c_24671,plain,(
    r2_hidden('#skF_10',k3_zfmisc_1('#skF_4','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24666,c_48])).

tff(c_24738,plain,(
    ! [A_2705,B_2706,C_2707] : k2_zfmisc_1(k2_zfmisc_1(A_2705,B_2706),C_2707) = k3_zfmisc_1(A_2705,B_2706,C_2707) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_25021,plain,(
    ! [A_2747,C_2748,A_2749,B_2750] :
      ( r2_hidden(k2_mcart_1(A_2747),C_2748)
      | ~ r2_hidden(A_2747,k3_zfmisc_1(A_2749,B_2750,C_2748)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24738,c_36])).

tff(c_25040,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_24671,c_25021])).

tff(c_25052,plain,(
    ! [B_2751] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2751)
      | ~ r1_tarski('#skF_9',B_2751) ) ),
    inference(resolution,[status(thm)],[c_25040,c_6])).

tff(c_25236,plain,(
    ! [B_2780,B_2781] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2780)
      | ~ r1_tarski(B_2781,B_2780)
      | ~ r1_tarski('#skF_9',B_2781) ) ),
    inference(resolution,[status(thm)],[c_25052,c_6])).

tff(c_25240,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_6')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_86,c_25236])).

tff(c_25248,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_25240])).

tff(c_24668,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24666,c_10381])).

tff(c_25133,plain,(
    ! [A_2763,B_2764,C_2765,D_2766] :
      ( k7_mcart_1(A_2763,B_2764,C_2765,D_2766) = k2_mcart_1(D_2766)
      | ~ m1_subset_1(D_2766,k3_zfmisc_1(A_2763,B_2764,C_2765))
      | k1_xboole_0 = C_2765
      | k1_xboole_0 = B_2764
      | k1_xboole_0 = A_2763 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_25137,plain,
    ( k7_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22488,c_25133])).

tff(c_25180,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_25137])).

tff(c_24786,plain,(
    ! [C_2714,B_2715,A_2716] :
      ( r2_hidden(C_2714,B_2715)
      | ~ r2_hidden(C_2714,A_2716)
      | ~ r1_tarski(A_2716,B_2715) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24839,plain,(
    ! [A_2721,B_2722] :
      ( r2_hidden('#skF_1'(A_2721),B_2722)
      | ~ r1_tarski(A_2721,B_2722)
      | v1_xboole_0(A_2721) ) ),
    inference(resolution,[status(thm)],[c_4,c_24786])).

tff(c_24860,plain,(
    ! [B_2723,A_2724] :
      ( ~ v1_xboole_0(B_2723)
      | ~ r1_tarski(A_2724,B_2723)
      | v1_xboole_0(A_2724) ) ),
    inference(resolution,[status(thm)],[c_24839,c_2])).

tff(c_24877,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(A_17)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_24860])).

tff(c_24878,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_24877])).

tff(c_24901,plain,(
    ! [A_2727,B_2728,C_2729] :
      ( ~ r1_xboole_0(A_2727,B_2728)
      | ~ r1_tarski(C_2729,B_2728)
      | ~ r1_tarski(C_2729,A_2727) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24878,c_26])).

tff(c_24988,plain,(
    ! [C_2741,B_2742,A_2743] :
      ( ~ r1_tarski(C_2741,B_2742)
      | ~ r1_tarski(C_2741,k4_xboole_0(A_2743,B_2742)) ) ),
    inference(resolution,[status(thm)],[c_28,c_24901])).

tff(c_24996,plain,(
    ! [B_2742] : ~ r1_tarski(k1_xboole_0,B_2742) ),
    inference(resolution,[status(thm)],[c_24,c_24988])).

tff(c_25001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24996])).

tff(c_25002,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_24877])).

tff(c_25182,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25180,c_25002])).

tff(c_25187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24668,c_25182])).

tff(c_25189,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_25137])).

tff(c_25229,plain,(
    ! [A_2776,B_2777,C_2778,D_2779] :
      ( k5_mcart_1(A_2776,B_2777,C_2778,D_2779) = k1_mcart_1(k1_mcart_1(D_2779))
      | ~ m1_subset_1(D_2779,k3_zfmisc_1(A_2776,B_2777,C_2778))
      | k1_xboole_0 = C_2778
      | k1_xboole_0 = B_2777
      | k1_xboole_0 = A_2776 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_25232,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22488,c_25229])).

tff(c_25235,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_10')) = k5_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_25189,c_25232])).

tff(c_25552,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_25235])).

tff(c_25565,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25552,c_25002])).

tff(c_24689,plain,(
    ! [A_2698,C_2699,B_2700] :
      ( r2_hidden(k2_mcart_1(A_2698),C_2699)
      | ~ r2_hidden(A_2698,k2_zfmisc_1(B_2700,C_2699)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_25684,plain,(
    ! [B_2824,C_2825] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2824,C_2825))),C_2825)
      | v1_xboole_0(k2_zfmisc_1(B_2824,C_2825)) ) ),
    inference(resolution,[status(thm)],[c_4,c_24689])).

tff(c_25731,plain,(
    ! [C_2827,B_2828] :
      ( ~ v1_xboole_0(C_2827)
      | v1_xboole_0(k2_zfmisc_1(B_2828,C_2827)) ) ),
    inference(resolution,[status(thm)],[c_25684,c_2])).

tff(c_25566,plain,(
    ! [A_2111] :
      ( A_2111 = '#skF_8'
      | ~ v1_xboole_0(A_2111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25552,c_18715])).

tff(c_25792,plain,(
    ! [B_2831,C_2832] :
      ( k2_zfmisc_1(B_2831,C_2832) = '#skF_8'
      | ~ v1_xboole_0(C_2832) ) ),
    inference(resolution,[status(thm)],[c_25731,c_25566])).

tff(c_25798,plain,(
    ! [B_2831] : k2_zfmisc_1(B_2831,'#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_25565,c_25792])).

tff(c_24808,plain,(
    ! [A_2717,B_2718,C_2719] :
      ( r2_hidden(k1_mcart_1(A_2717),B_2718)
      | ~ r2_hidden(A_2717,k2_zfmisc_1(B_2718,C_2719)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_25998,plain,(
    ! [A_2846,A_2847,B_2848,C_2849] :
      ( r2_hidden(k1_mcart_1(A_2846),k2_zfmisc_1(A_2847,B_2848))
      | ~ r2_hidden(A_2846,k3_zfmisc_1(A_2847,B_2848,C_2849)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_24808])).

tff(c_26031,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_24671,c_25998])).

tff(c_26055,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25798,c_26031])).

tff(c_25385,plain,(
    ! [A_2803,B_2804,B_2805] :
      ( r2_hidden('#skF_3'(A_2803,B_2804),B_2805)
      | ~ r1_tarski(A_2803,B_2805)
      | r1_xboole_0(A_2803,B_2804) ) ),
    inference(resolution,[status(thm)],[c_16,c_24786])).

tff(c_25414,plain,(
    ! [B_2806,A_2807,B_2808] :
      ( ~ v1_xboole_0(B_2806)
      | ~ r1_tarski(A_2807,B_2806)
      | r1_xboole_0(A_2807,B_2808) ) ),
    inference(resolution,[status(thm)],[c_25385,c_2])).

tff(c_25426,plain,(
    ! [A_17,B_2808] :
      ( ~ v1_xboole_0(A_17)
      | r1_xboole_0(k1_xboole_0,B_2808) ) ),
    inference(resolution,[status(thm)],[c_24,c_25414])).

tff(c_25427,plain,(
    ! [A_17] : ~ v1_xboole_0(A_17) ),
    inference(splitLeft,[status(thm)],[c_25426])).

tff(c_25437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25427,c_25002])).

tff(c_25438,plain,(
    ! [B_2808] : r1_xboole_0(k1_xboole_0,B_2808) ),
    inference(splitRight,[status(thm)],[c_25426])).

tff(c_25576,plain,(
    ! [B_2817] : r1_xboole_0('#skF_8',B_2817) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25552,c_25438])).

tff(c_25582,plain,(
    ! [C_14,B_2817] :
      ( ~ r2_hidden(C_14,B_2817)
      | ~ r2_hidden(C_14,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_25576,c_12])).

tff(c_26061,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_10'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_26055,c_25582])).

tff(c_26070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26055,c_26061])).

tff(c_26072,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_25235])).

tff(c_25318,plain,(
    ! [A_2785,B_2786,C_2787,D_2788] :
      ( k6_mcart_1(A_2785,B_2786,C_2787,D_2788) = k2_mcart_1(k1_mcart_1(D_2788))
      | ~ m1_subset_1(D_2788,k3_zfmisc_1(A_2785,B_2786,C_2787))
      | k1_xboole_0 = C_2787
      | k1_xboole_0 = B_2786
      | k1_xboole_0 = A_2785 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_25321,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22488,c_25318])).

tff(c_25324,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_25189,c_25321])).

tff(c_26077,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_26072,c_25324])).

tff(c_26078,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_26077])).

tff(c_25439,plain,(
    ! [B_2809] : r1_xboole_0(k1_xboole_0,B_2809) ),
    inference(splitRight,[status(thm)],[c_25426])).

tff(c_25446,plain,(
    ! [C_2810,B_2811] :
      ( ~ r2_hidden(C_2810,B_2811)
      | ~ r2_hidden(C_2810,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_25439,c_12])).

tff(c_25478,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_25040,c_25446])).

tff(c_26083,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26078,c_25478])).

tff(c_26099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25248,c_26083])).

tff(c_26100,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10') ),
    inference(splitRight,[status(thm)],[c_26077])).

tff(c_26848,plain,(
    ! [A_2912,A_2913,B_2914,C_2915] :
      ( r2_hidden(k1_mcart_1(A_2912),k2_zfmisc_1(A_2913,B_2914))
      | ~ r2_hidden(A_2912,k3_zfmisc_1(A_2913,B_2914,C_2915)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_24808])).

tff(c_26912,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_4','#skF_8')) ),
    inference(resolution,[status(thm)],[c_24671,c_26848])).

tff(c_26922,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_26912,c_36])).

tff(c_26930,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_8','#skF_6','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26100,c_26922])).

tff(c_26932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22485,c_26930])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:12:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.49/4.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.42/4.38  
% 11.42/4.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.42/4.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 11.42/4.38  
% 11.42/4.38  %Foreground sorts:
% 11.42/4.38  
% 11.42/4.38  
% 11.42/4.38  %Background operators:
% 11.42/4.38  
% 11.42/4.38  
% 11.42/4.38  %Foreground operators:
% 11.42/4.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.42/4.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.42/4.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.42/4.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.42/4.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.42/4.38  tff('#skF_7', type, '#skF_7': $i).
% 11.42/4.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.42/4.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.42/4.38  tff('#skF_10', type, '#skF_10': $i).
% 11.42/4.38  tff('#skF_5', type, '#skF_5': $i).
% 11.42/4.38  tff('#skF_6', type, '#skF_6': $i).
% 11.42/4.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.42/4.38  tff('#skF_9', type, '#skF_9': $i).
% 11.42/4.38  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 11.42/4.38  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 11.42/4.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.42/4.38  tff('#skF_8', type, '#skF_8': $i).
% 11.42/4.38  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 11.42/4.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.42/4.38  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 11.42/4.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.42/4.38  tff('#skF_4', type, '#skF_4': $i).
% 11.42/4.38  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 11.42/4.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.42/4.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.42/4.38  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 11.42/4.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.42/4.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.42/4.38  
% 11.42/4.46  tff(f_64, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.42/4.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.42/4.46  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.42/4.46  tff(f_76, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 11.42/4.46  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.42/4.46  tff(f_74, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 11.42/4.46  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.42/4.46  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 11.42/4.46  tff(f_82, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 11.42/4.46  tff(f_88, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 11.42/4.46  tff(f_80, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.42/4.46  tff(f_108, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 11.42/4.46  tff(c_24, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.42/4.46  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.42/4.46  tff(c_20408, plain, (![C_2293, B_2294, A_2295]: (r2_hidden(C_2293, B_2294) | ~r2_hidden(C_2293, A_2295) | ~r1_tarski(A_2295, B_2294))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_20478, plain, (![A_2303, B_2304]: (r2_hidden('#skF_1'(A_2303), B_2304) | ~r1_tarski(A_2303, B_2304) | v1_xboole_0(A_2303))), inference(resolution, [status(thm)], [c_4, c_20408])).
% 11.42/4.46  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.42/4.46  tff(c_20499, plain, (![B_2305, A_2306]: (~v1_xboole_0(B_2305) | ~r1_tarski(A_2306, B_2305) | v1_xboole_0(A_2306))), inference(resolution, [status(thm)], [c_20478, c_2])).
% 11.42/4.46  tff(c_20520, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_20499])).
% 11.42/4.46  tff(c_20521, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_20520])).
% 11.42/4.46  tff(c_20524, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_20521, c_4])).
% 11.42/4.46  tff(c_20429, plain, (![A_1, B_2294]: (r2_hidden('#skF_1'(A_1), B_2294) | ~r1_tarski(A_1, B_2294) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_20408])).
% 11.42/4.46  tff(c_20544, plain, (![A_2311, B_2312]: (r2_hidden('#skF_1'(A_2311), B_2312) | ~r1_tarski(A_2311, B_2312))), inference(negUnitSimplification, [status(thm)], [c_20521, c_20429])).
% 11.42/4.46  tff(c_28, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.42/4.46  tff(c_20377, plain, (![A_2287, B_2288, C_2289]: (~r1_xboole_0(A_2287, B_2288) | ~r2_hidden(C_2289, B_2288) | ~r2_hidden(C_2289, A_2287))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.42/4.46  tff(c_20386, plain, (![C_2289, B_22, A_21]: (~r2_hidden(C_2289, B_22) | ~r2_hidden(C_2289, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_28, c_20377])).
% 11.42/4.46  tff(c_20643, plain, (![A_2323, B_2324, A_2325]: (~r2_hidden('#skF_1'(A_2323), B_2324) | ~r1_tarski(A_2323, k4_xboole_0(A_2325, B_2324)))), inference(resolution, [status(thm)], [c_20544, c_20386])).
% 11.42/4.46  tff(c_20655, plain, (![A_2329, A_2330]: (~r1_tarski(A_2329, k4_xboole_0(A_2330, A_2329)))), inference(resolution, [status(thm)], [c_20524, c_20643])).
% 11.42/4.46  tff(c_20660, plain, $false, inference(resolution, [status(thm)], [c_24, c_20655])).
% 11.42/4.46  tff(c_20661, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_20520])).
% 11.42/4.46  tff(c_17375, plain, (![C_1958, B_1959, A_1960]: (r2_hidden(C_1958, B_1959) | ~r2_hidden(C_1958, A_1960) | ~r1_tarski(A_1960, B_1959))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_17475, plain, (![A_1974, B_1975]: (r2_hidden('#skF_1'(A_1974), B_1975) | ~r1_tarski(A_1974, B_1975) | v1_xboole_0(A_1974))), inference(resolution, [status(thm)], [c_4, c_17375])).
% 11.42/4.46  tff(c_17496, plain, (![B_1976, A_1977]: (~v1_xboole_0(B_1976) | ~r1_tarski(A_1977, B_1976) | v1_xboole_0(A_1977))), inference(resolution, [status(thm)], [c_17475, c_2])).
% 11.42/4.46  tff(c_17508, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_17496])).
% 11.42/4.46  tff(c_17509, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_17508])).
% 11.42/4.46  tff(c_26, plain, (![A_18, B_19, C_20]: (~r1_xboole_0(A_18, B_19) | ~r1_tarski(C_20, B_19) | ~r1_tarski(C_20, A_18) | v1_xboole_0(C_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.42/4.46  tff(c_17637, plain, (![A_1997, B_1998, C_1999]: (~r1_xboole_0(A_1997, B_1998) | ~r1_tarski(C_1999, B_1998) | ~r1_tarski(C_1999, A_1997))), inference(negUnitSimplification, [status(thm)], [c_17509, c_26])).
% 11.42/4.46  tff(c_17641, plain, (![C_2000, B_2001, A_2002]: (~r1_tarski(C_2000, B_2001) | ~r1_tarski(C_2000, k4_xboole_0(A_2002, B_2001)))), inference(resolution, [status(thm)], [c_28, c_17637])).
% 11.42/4.46  tff(c_17649, plain, (![B_2001]: (~r1_tarski(k1_xboole_0, B_2001))), inference(resolution, [status(thm)], [c_24, c_17641])).
% 11.42/4.46  tff(c_17654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_17649])).
% 11.42/4.46  tff(c_17655, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_17508])).
% 11.42/4.46  tff(c_22, plain, (![B_16]: (r1_tarski(B_16, B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.42/4.46  tff(c_15631, plain, (![C_1787, B_1788, A_1789]: (r2_hidden(C_1787, B_1788) | ~r2_hidden(C_1787, A_1789) | ~r1_tarski(A_1789, B_1788))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_15741, plain, (![A_1806, B_1807]: (r2_hidden('#skF_1'(A_1806), B_1807) | ~r1_tarski(A_1806, B_1807) | v1_xboole_0(A_1806))), inference(resolution, [status(thm)], [c_4, c_15631])).
% 11.42/4.46  tff(c_15762, plain, (![B_1808, A_1809]: (~v1_xboole_0(B_1808) | ~r1_tarski(A_1809, B_1808) | v1_xboole_0(A_1809))), inference(resolution, [status(thm)], [c_15741, c_2])).
% 11.42/4.46  tff(c_15779, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_15762])).
% 11.42/4.46  tff(c_15780, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_15779])).
% 11.42/4.46  tff(c_15847, plain, (![A_1817, B_1818, C_1819]: (~r1_xboole_0(A_1817, B_1818) | ~r1_tarski(C_1819, B_1818) | ~r1_tarski(C_1819, A_1817))), inference(negUnitSimplification, [status(thm)], [c_15780, c_26])).
% 11.42/4.46  tff(c_15902, plain, (![C_1829, B_1830, A_1831]: (~r1_tarski(C_1829, B_1830) | ~r1_tarski(C_1829, k4_xboole_0(A_1831, B_1830)))), inference(resolution, [status(thm)], [c_28, c_15847])).
% 11.42/4.46  tff(c_15910, plain, (![B_1830]: (~r1_tarski(k1_xboole_0, B_1830))), inference(resolution, [status(thm)], [c_24, c_15902])).
% 11.42/4.46  tff(c_15915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_15910])).
% 11.42/4.46  tff(c_15916, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_15779])).
% 11.42/4.46  tff(c_48, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.42/4.46  tff(c_34, plain, (![A_25, B_26, C_27]: (k2_zfmisc_1(k2_zfmisc_1(A_25, B_26), C_27)=k3_zfmisc_1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.42/4.46  tff(c_15650, plain, (![A_1790, C_1791, B_1792]: (r2_hidden(k2_mcart_1(A_1790), C_1791) | ~r2_hidden(A_1790, k2_zfmisc_1(B_1792, C_1791)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.46  tff(c_15925, plain, (![A_1832, C_1833, A_1834, B_1835]: (r2_hidden(k2_mcart_1(A_1832), C_1833) | ~r2_hidden(A_1832, k3_zfmisc_1(A_1834, B_1835, C_1833)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_15650])).
% 11.42/4.46  tff(c_15947, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_48, c_15925])).
% 11.42/4.46  tff(c_14185, plain, (![A_1580, B_1581]: (r2_hidden('#skF_2'(A_1580, B_1581), A_1580) | r1_tarski(A_1580, B_1581))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_14195, plain, (![A_1580, B_1581]: (~v1_xboole_0(A_1580) | r1_tarski(A_1580, B_1581))), inference(resolution, [status(thm)], [c_14185, c_2])).
% 11.42/4.46  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.42/4.46  tff(c_72, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.42/4.46  tff(c_88, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_72])).
% 11.42/4.46  tff(c_10383, plain, (![B_1106, A_1107]: (B_1106=A_1107 | ~r1_tarski(B_1106, A_1107) | ~r1_tarski(A_1107, B_1106))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.42/4.46  tff(c_10394, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_88, c_10383])).
% 11.42/4.46  tff(c_15585, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_10394])).
% 11.42/4.46  tff(c_15589, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_14195, c_15585])).
% 11.42/4.46  tff(c_14265, plain, (![C_1593, B_1594, A_1595]: (r2_hidden(C_1593, B_1594) | ~r2_hidden(C_1593, A_1595) | ~r1_tarski(A_1595, B_1594))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_14380, plain, (![A_1612, B_1613]: (r2_hidden('#skF_1'(A_1612), B_1613) | ~r1_tarski(A_1612, B_1613) | v1_xboole_0(A_1612))), inference(resolution, [status(thm)], [c_4, c_14265])).
% 11.42/4.46  tff(c_14401, plain, (![B_1614, A_1615]: (~v1_xboole_0(B_1614) | ~r1_tarski(A_1615, B_1614) | v1_xboole_0(A_1615))), inference(resolution, [status(thm)], [c_14380, c_2])).
% 11.42/4.46  tff(c_14422, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_14401])).
% 11.42/4.46  tff(c_14423, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_14422])).
% 11.42/4.46  tff(c_14426, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_14423, c_4])).
% 11.42/4.46  tff(c_14283, plain, (![A_1, B_1594]: (r2_hidden('#skF_1'(A_1), B_1594) | ~r1_tarski(A_1, B_1594) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_14265])).
% 11.42/4.46  tff(c_14446, plain, (![A_1620, B_1621]: (r2_hidden('#skF_1'(A_1620), B_1621) | ~r1_tarski(A_1620, B_1621))), inference(negUnitSimplification, [status(thm)], [c_14423, c_14283])).
% 11.42/4.46  tff(c_14299, plain, (![A_1599, B_1600, C_1601]: (~r1_xboole_0(A_1599, B_1600) | ~r2_hidden(C_1601, B_1600) | ~r2_hidden(C_1601, A_1599))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.42/4.46  tff(c_14308, plain, (![C_1601, B_22, A_21]: (~r2_hidden(C_1601, B_22) | ~r2_hidden(C_1601, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_28, c_14299])).
% 11.42/4.46  tff(c_14545, plain, (![A_1632, B_1633, A_1634]: (~r2_hidden('#skF_1'(A_1632), B_1633) | ~r1_tarski(A_1632, k4_xboole_0(A_1634, B_1633)))), inference(resolution, [status(thm)], [c_14446, c_14308])).
% 11.42/4.46  tff(c_14557, plain, (![A_1638, A_1639]: (~r1_tarski(A_1638, k4_xboole_0(A_1639, A_1638)))), inference(resolution, [status(thm)], [c_14426, c_14545])).
% 11.42/4.46  tff(c_14562, plain, $false, inference(resolution, [status(thm)], [c_24, c_14557])).
% 11.42/4.46  tff(c_14563, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_14422])).
% 11.42/4.46  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.42/4.46  tff(c_87, plain, (r1_tarski('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_72])).
% 11.42/4.46  tff(c_10395, plain, ('#skF_5'='#skF_8' | ~r1_tarski('#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_87, c_10383])).
% 11.42/4.46  tff(c_14222, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_10395])).
% 11.42/4.46  tff(c_14226, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_14195, c_14222])).
% 11.42/4.46  tff(c_14361, plain, (![A_1609, C_1610, B_1611]: (r2_hidden(k2_mcart_1(A_1609), C_1610) | ~r2_hidden(A_1609, k2_zfmisc_1(B_1611, C_1610)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.46  tff(c_14572, plain, (![A_1640, C_1641, A_1642, B_1643]: (r2_hidden(k2_mcart_1(A_1640), C_1641) | ~r2_hidden(A_1640, k3_zfmisc_1(A_1642, B_1643, C_1641)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_14361])).
% 11.42/4.46  tff(c_14594, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_48, c_14572])).
% 11.42/4.46  tff(c_14233, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_10394])).
% 11.42/4.46  tff(c_14237, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_14195, c_14233])).
% 11.42/4.46  tff(c_10416, plain, (![A_1109, B_1110]: (r2_hidden('#skF_2'(A_1109, B_1110), A_1109) | r1_tarski(A_1109, B_1110))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_10427, plain, (![A_1111, B_1112]: (~v1_xboole_0(A_1111) | r1_tarski(A_1111, B_1112))), inference(resolution, [status(thm)], [c_10416, c_2])).
% 11.42/4.46  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.42/4.46  tff(c_86, plain, (r1_tarski('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_72])).
% 11.42/4.46  tff(c_10396, plain, ('#skF_6'='#skF_9' | ~r1_tarski('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_86, c_10383])).
% 11.42/4.46  tff(c_10415, plain, (~r1_tarski('#skF_6', '#skF_9')), inference(splitLeft, [status(thm)], [c_10396])).
% 11.42/4.46  tff(c_10437, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_10427, c_10415])).
% 11.42/4.46  tff(c_11708, plain, (![C_1302, B_1303, A_1304]: (r2_hidden(C_1302, B_1303) | ~r2_hidden(C_1302, A_1304) | ~r1_tarski(A_1304, B_1303))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_11860, plain, (![A_1328, B_1329]: (r2_hidden('#skF_1'(A_1328), B_1329) | ~r1_tarski(A_1328, B_1329) | v1_xboole_0(A_1328))), inference(resolution, [status(thm)], [c_4, c_11708])).
% 11.42/4.46  tff(c_11881, plain, (![B_1330, A_1331]: (~v1_xboole_0(B_1330) | ~r1_tarski(A_1331, B_1330) | v1_xboole_0(A_1331))), inference(resolution, [status(thm)], [c_11860, c_2])).
% 11.42/4.46  tff(c_11902, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_11881])).
% 11.42/4.46  tff(c_11924, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_11902])).
% 11.42/4.46  tff(c_11948, plain, (![A_1337, B_1338, C_1339]: (~r1_xboole_0(A_1337, B_1338) | ~r1_tarski(C_1339, B_1338) | ~r1_tarski(C_1339, A_1337))), inference(negUnitSimplification, [status(thm)], [c_11924, c_26])).
% 11.42/4.46  tff(c_12025, plain, (![C_1351, B_1352, A_1353]: (~r1_tarski(C_1351, B_1352) | ~r1_tarski(C_1351, k4_xboole_0(A_1353, B_1352)))), inference(resolution, [status(thm)], [c_28, c_11948])).
% 11.42/4.46  tff(c_12033, plain, (![B_1352]: (~r1_tarski(k1_xboole_0, B_1352))), inference(resolution, [status(thm)], [c_24, c_12025])).
% 11.42/4.46  tff(c_12038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_12033])).
% 11.42/4.46  tff(c_12039, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_11902])).
% 11.42/4.46  tff(c_11800, plain, (![A_1316, C_1317, B_1318]: (r2_hidden(k2_mcart_1(A_1316), C_1317) | ~r2_hidden(A_1316, k2_zfmisc_1(B_1318, C_1317)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.46  tff(c_12102, plain, (![A_1364, C_1365, A_1366, B_1367]: (r2_hidden(k2_mcart_1(A_1364), C_1365) | ~r2_hidden(A_1364, k3_zfmisc_1(A_1366, B_1367, C_1365)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_11800])).
% 11.42/4.46  tff(c_12128, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_48, c_12102])).
% 11.42/4.46  tff(c_10426, plain, (![A_1109, B_1110]: (~v1_xboole_0(A_1109) | r1_tarski(A_1109, B_1110))), inference(resolution, [status(thm)], [c_10416, c_2])).
% 11.42/4.46  tff(c_11703, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_10394])).
% 11.42/4.46  tff(c_11707, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_10426, c_11703])).
% 11.42/4.46  tff(c_10440, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_10395])).
% 11.42/4.46  tff(c_10444, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_10426, c_10440])).
% 11.42/4.46  tff(c_10568, plain, (![C_1137, B_1138, A_1139]: (r2_hidden(C_1137, B_1138) | ~r2_hidden(C_1137, A_1139) | ~r1_tarski(A_1139, B_1138))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_10599, plain, (![A_1141, B_1142]: (r2_hidden('#skF_1'(A_1141), B_1142) | ~r1_tarski(A_1141, B_1142) | v1_xboole_0(A_1141))), inference(resolution, [status(thm)], [c_4, c_10568])).
% 11.42/4.46  tff(c_10620, plain, (![B_1143, A_1144]: (~v1_xboole_0(B_1143) | ~r1_tarski(A_1144, B_1143) | v1_xboole_0(A_1144))), inference(resolution, [status(thm)], [c_10599, c_2])).
% 11.42/4.46  tff(c_10645, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_10620])).
% 11.42/4.46  tff(c_10667, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_10645])).
% 11.42/4.46  tff(c_10691, plain, (![A_1150, B_1151, C_1152]: (~r1_xboole_0(A_1150, B_1151) | ~r1_tarski(C_1152, B_1151) | ~r1_tarski(C_1152, A_1150))), inference(negUnitSimplification, [status(thm)], [c_10667, c_26])).
% 11.42/4.46  tff(c_10768, plain, (![C_1164, B_1165, A_1166]: (~r1_tarski(C_1164, B_1165) | ~r1_tarski(C_1164, k4_xboole_0(A_1166, B_1165)))), inference(resolution, [status(thm)], [c_28, c_10691])).
% 11.42/4.46  tff(c_10776, plain, (![B_1165]: (~r1_tarski(k1_xboole_0, B_1165))), inference(resolution, [status(thm)], [c_24, c_10768])).
% 11.42/4.46  tff(c_10781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_10776])).
% 11.42/4.46  tff(c_10782, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_10645])).
% 11.42/4.46  tff(c_10549, plain, (![A_1134, C_1135, B_1136]: (r2_hidden(k2_mcart_1(A_1134), C_1135) | ~r2_hidden(A_1134, k2_zfmisc_1(B_1136, C_1135)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.46  tff(c_10857, plain, (![A_1181, C_1182, A_1183, B_1184]: (r2_hidden(k2_mcart_1(A_1181), C_1182) | ~r2_hidden(A_1181, k3_zfmisc_1(A_1183, B_1184, C_1182)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_10549])).
% 11.42/4.46  tff(c_10883, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_48, c_10857])).
% 11.42/4.46  tff(c_10446, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_10394])).
% 11.42/4.46  tff(c_10450, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_10426, c_10446])).
% 11.42/4.46  tff(c_50, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.42/4.46  tff(c_10892, plain, (![A_1185, B_1186, C_1187, D_1188]: (k7_mcart_1(A_1185, B_1186, C_1187, D_1188)=k2_mcart_1(D_1188) | ~m1_subset_1(D_1188, k3_zfmisc_1(A_1185, B_1186, C_1187)) | k1_xboole_0=C_1187 | k1_xboole_0=B_1186 | k1_xboole_0=A_1185)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.46  tff(c_10896, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_10892])).
% 11.42/4.46  tff(c_10944, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_10896])).
% 11.42/4.46  tff(c_10946, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10944, c_10782])).
% 11.42/4.46  tff(c_10951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10450, c_10946])).
% 11.42/4.46  tff(c_10952, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_10896])).
% 11.42/4.46  tff(c_11081, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_10952])).
% 11.42/4.46  tff(c_7400, plain, (![C_795, B_796, A_797]: (r2_hidden(C_795, B_796) | ~r2_hidden(C_795, A_797) | ~r1_tarski(A_797, B_796))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_7513, plain, (![A_814, B_815]: (r2_hidden('#skF_1'(A_814), B_815) | ~r1_tarski(A_814, B_815) | v1_xboole_0(A_814))), inference(resolution, [status(thm)], [c_4, c_7400])).
% 11.42/4.46  tff(c_7534, plain, (![B_816, A_817]: (~v1_xboole_0(B_816) | ~r1_tarski(A_817, B_816) | v1_xboole_0(A_817))), inference(resolution, [status(thm)], [c_7513, c_2])).
% 11.42/4.46  tff(c_7550, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_7534])).
% 11.42/4.46  tff(c_7561, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_7550])).
% 11.42/4.46  tff(c_7655, plain, (![A_837, B_838, C_839]: (~r1_xboole_0(A_837, B_838) | ~r1_tarski(C_839, B_838) | ~r1_tarski(C_839, A_837))), inference(negUnitSimplification, [status(thm)], [c_7561, c_26])).
% 11.42/4.46  tff(c_7659, plain, (![C_840, B_841, A_842]: (~r1_tarski(C_840, B_841) | ~r1_tarski(C_840, k4_xboole_0(A_842, B_841)))), inference(resolution, [status(thm)], [c_28, c_7655])).
% 11.42/4.46  tff(c_7667, plain, (![B_841]: (~r1_tarski(k1_xboole_0, B_841))), inference(resolution, [status(thm)], [c_24, c_7659])).
% 11.42/4.46  tff(c_7672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_7667])).
% 11.42/4.46  tff(c_7673, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_7550])).
% 11.42/4.46  tff(c_167, plain, (![C_76, B_77, A_78]: (r2_hidden(C_76, B_77) | ~r2_hidden(C_76, A_78) | ~r1_tarski(A_78, B_77))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_310, plain, (![A_99, B_100]: (r2_hidden('#skF_1'(A_99), B_100) | ~r1_tarski(A_99, B_100) | v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_4, c_167])).
% 11.42/4.46  tff(c_331, plain, (![B_101, A_102]: (~v1_xboole_0(B_101) | ~r1_tarski(A_102, B_101) | v1_xboole_0(A_102))), inference(resolution, [status(thm)], [c_310, c_2])).
% 11.42/4.46  tff(c_355, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_331])).
% 11.42/4.46  tff(c_356, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_355])).
% 11.42/4.46  tff(c_413, plain, (![A_114, B_115, C_116]: (~r1_xboole_0(A_114, B_115) | ~r1_tarski(C_116, B_115) | ~r1_tarski(C_116, A_114))), inference(negUnitSimplification, [status(thm)], [c_356, c_26])).
% 11.42/4.46  tff(c_464, plain, (![C_125, B_126, A_127]: (~r1_tarski(C_125, B_126) | ~r1_tarski(C_125, k4_xboole_0(A_127, B_126)))), inference(resolution, [status(thm)], [c_28, c_413])).
% 11.42/4.46  tff(c_472, plain, (![B_126]: (~r1_tarski(k1_xboole_0, B_126))), inference(resolution, [status(thm)], [c_24, c_464])).
% 11.42/4.46  tff(c_477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_472])).
% 11.42/4.46  tff(c_478, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_355])).
% 11.42/4.46  tff(c_46, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9') | ~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8') | ~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 11.42/4.46  tff(c_96, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_46])).
% 11.42/4.46  tff(c_97, plain, (![A_64, B_65]: (r2_hidden('#skF_2'(A_64, B_65), A_64) | r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_107, plain, (![A_64, B_65]: (~v1_xboole_0(A_64) | r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_97, c_2])).
% 11.42/4.46  tff(c_109, plain, (![B_68, A_69]: (B_68=A_69 | ~r1_tarski(B_68, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.42/4.46  tff(c_124, plain, ('#skF_5'='#skF_8' | ~r1_tarski('#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_87, c_109])).
% 11.42/4.46  tff(c_156, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_124])).
% 11.42/4.46  tff(c_161, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_107, c_156])).
% 11.42/4.46  tff(c_123, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_88, c_109])).
% 11.42/4.46  tff(c_166, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_123])).
% 11.42/4.46  tff(c_186, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_107, c_166])).
% 11.42/4.46  tff(c_622, plain, (![A_151, B_152, C_153, D_154]: (k7_mcart_1(A_151, B_152, C_153, D_154)=k2_mcart_1(D_154) | ~m1_subset_1(D_154, k3_zfmisc_1(A_151, B_152, C_153)) | k1_xboole_0=C_153 | k1_xboole_0=B_152 | k1_xboole_0=A_151)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.46  tff(c_626, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_622])).
% 11.42/4.46  tff(c_663, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_626])).
% 11.42/4.46  tff(c_665, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_663, c_478])).
% 11.42/4.46  tff(c_670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_665])).
% 11.42/4.46  tff(c_672, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_626])).
% 11.42/4.46  tff(c_757, plain, (![A_168, B_169, C_170, D_171]: (k6_mcart_1(A_168, B_169, C_170, D_171)=k2_mcart_1(k1_mcart_1(D_171)) | ~m1_subset_1(D_171, k3_zfmisc_1(A_168, B_169, C_170)) | k1_xboole_0=C_170 | k1_xboole_0=B_169 | k1_xboole_0=A_168)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.46  tff(c_760, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_757])).
% 11.42/4.46  tff(c_763, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_672, c_760])).
% 11.42/4.46  tff(c_779, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_763])).
% 11.42/4.46  tff(c_785, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_779, c_478])).
% 11.42/4.46  tff(c_790, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_785])).
% 11.42/4.46  tff(c_792, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_763])).
% 11.42/4.46  tff(c_679, plain, (![A_158, B_159, C_160, D_161]: (k5_mcart_1(A_158, B_159, C_160, D_161)=k1_mcart_1(k1_mcart_1(D_161)) | ~m1_subset_1(D_161, k3_zfmisc_1(A_158, B_159, C_160)) | k1_xboole_0=C_160 | k1_xboole_0=B_159 | k1_xboole_0=A_158)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.46  tff(c_682, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_679])).
% 11.42/4.46  tff(c_685, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_672, c_682])).
% 11.42/4.46  tff(c_883, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_792, c_685])).
% 11.42/4.46  tff(c_884, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_883])).
% 11.42/4.46  tff(c_291, plain, (![A_96, B_97, C_98]: (k2_zfmisc_1(k2_zfmisc_1(A_96, B_97), C_98)=k3_zfmisc_1(A_96, B_97, C_98))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.42/4.46  tff(c_36, plain, (![A_28, C_30, B_29]: (r2_hidden(k2_mcart_1(A_28), C_30) | ~r2_hidden(A_28, k2_zfmisc_1(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.46  tff(c_487, plain, (![A_128, C_129, A_130, B_131]: (r2_hidden(k2_mcart_1(A_128), C_129) | ~r2_hidden(A_128, k3_zfmisc_1(A_130, B_131, C_129)))), inference(superposition, [status(thm), theory('equality')], [c_291, c_36])).
% 11.42/4.46  tff(c_509, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_48, c_487])).
% 11.42/4.46  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.46  tff(c_528, plain, (![B_135]: (r2_hidden(k2_mcart_1('#skF_10'), B_135) | ~r1_tarski('#skF_9', B_135))), inference(resolution, [status(thm)], [c_509, c_6])).
% 11.42/4.46  tff(c_627, plain, (![B_155, B_156]: (r2_hidden(k2_mcart_1('#skF_10'), B_155) | ~r1_tarski(B_156, B_155) | ~r1_tarski('#skF_9', B_156))), inference(resolution, [status(thm)], [c_528, c_6])).
% 11.42/4.46  tff(c_647, plain, (![A_17]: (r2_hidden(k2_mcart_1('#skF_10'), A_17) | ~r1_tarski('#skF_9', k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_627])).
% 11.42/4.46  tff(c_678, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_647])).
% 11.42/4.46  tff(c_889, plain, (~r1_tarski('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_884, c_678])).
% 11.42/4.46  tff(c_899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_889])).
% 11.42/4.46  tff(c_900, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_883])).
% 11.42/4.46  tff(c_38, plain, (![A_28, B_29, C_30]: (r2_hidden(k1_mcart_1(A_28), B_29) | ~r2_hidden(A_28, k2_zfmisc_1(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.46  tff(c_2073, plain, (![A_283, A_284, B_285, C_286]: (r2_hidden(k1_mcart_1(A_283), k2_zfmisc_1(A_284, B_285)) | ~r2_hidden(A_283, k3_zfmisc_1(A_284, B_285, C_286)))), inference(superposition, [status(thm), theory('equality')], [c_291, c_38])).
% 11.42/4.46  tff(c_2138, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_48, c_2073])).
% 11.42/4.46  tff(c_2147, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_7')), inference(resolution, [status(thm)], [c_2138, c_38])).
% 11.42/4.46  tff(c_2158, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_900, c_2147])).
% 11.42/4.46  tff(c_2160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_2158])).
% 11.42/4.46  tff(c_2162, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_647])).
% 11.42/4.46  tff(c_552, plain, (![B_135]: (~v1_xboole_0(B_135) | ~r1_tarski('#skF_9', B_135))), inference(resolution, [status(thm)], [c_528, c_2])).
% 11.42/4.46  tff(c_2167, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2162, c_552])).
% 11.42/4.46  tff(c_2185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_478, c_2167])).
% 11.42/4.46  tff(c_2186, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_123])).
% 11.42/4.46  tff(c_2188, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_96])).
% 11.42/4.46  tff(c_2191, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_48])).
% 11.42/4.46  tff(c_2599, plain, (![A_345, B_346, C_347, D_348]: (k7_mcart_1(A_345, B_346, C_347, D_348)=k2_mcart_1(D_348) | ~m1_subset_1(D_348, k3_zfmisc_1(A_345, B_346, C_347)) | k1_xboole_0=C_347 | k1_xboole_0=B_346 | k1_xboole_0=A_345)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.46  tff(c_2603, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_2599])).
% 11.42/4.46  tff(c_2621, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2603])).
% 11.42/4.47  tff(c_2626, plain, (![A_17]: (r1_tarski('#skF_4', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_2621, c_24])).
% 11.42/4.47  tff(c_16, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), A_10) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.42/4.47  tff(c_2284, plain, (![C_300, B_301, A_302]: (r2_hidden(C_300, B_301) | ~r2_hidden(C_300, A_302) | ~r1_tarski(A_302, B_301))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.47  tff(c_2816, plain, (![A_383, B_384, B_385]: (r2_hidden('#skF_3'(A_383, B_384), B_385) | ~r1_tarski(A_383, B_385) | r1_xboole_0(A_383, B_384))), inference(resolution, [status(thm)], [c_16, c_2284])).
% 11.42/4.47  tff(c_2841, plain, (![B_386, A_387, B_388]: (~v1_xboole_0(B_386) | ~r1_tarski(A_387, B_386) | r1_xboole_0(A_387, B_388))), inference(resolution, [status(thm)], [c_2816, c_2])).
% 11.42/4.47  tff(c_2852, plain, (![A_17, B_388]: (~v1_xboole_0(A_17) | r1_xboole_0('#skF_4', B_388))), inference(resolution, [status(thm)], [c_2626, c_2841])).
% 11.42/4.47  tff(c_2857, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_2852])).
% 11.42/4.47  tff(c_2331, plain, (![A_309, B_310]: (r2_hidden('#skF_1'(A_309), B_310) | ~r1_tarski(A_309, B_310) | v1_xboole_0(A_309))), inference(resolution, [status(thm)], [c_4, c_2284])).
% 11.42/4.47  tff(c_2352, plain, (![B_311, A_312]: (~v1_xboole_0(B_311) | ~r1_tarski(A_312, B_311) | v1_xboole_0(A_312))), inference(resolution, [status(thm)], [c_2331, c_2])).
% 11.42/4.47  tff(c_2372, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_2352])).
% 11.42/4.47  tff(c_2373, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_2372])).
% 11.42/4.47  tff(c_2479, plain, (![A_329, B_330, C_331]: (~r1_xboole_0(A_329, B_330) | ~r1_tarski(C_331, B_330) | ~r1_tarski(C_331, A_329))), inference(negUnitSimplification, [status(thm)], [c_2373, c_26])).
% 11.42/4.47  tff(c_2483, plain, (![C_332, B_333, A_334]: (~r1_tarski(C_332, B_333) | ~r1_tarski(C_332, k4_xboole_0(A_334, B_333)))), inference(resolution, [status(thm)], [c_28, c_2479])).
% 11.42/4.47  tff(c_2491, plain, (![B_333]: (~r1_tarski(k1_xboole_0, B_333))), inference(resolution, [status(thm)], [c_24, c_2483])).
% 11.42/4.47  tff(c_2496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_2491])).
% 11.42/4.47  tff(c_2497, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_2372])).
% 11.42/4.47  tff(c_2623, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2621, c_2497])).
% 11.42/4.47  tff(c_2866, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2857, c_2623])).
% 11.42/4.47  tff(c_2873, plain, (![B_392]: (r1_xboole_0('#skF_4', B_392))), inference(splitRight, [status(thm)], [c_2852])).
% 11.42/4.47  tff(c_12, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, B_11) | ~r2_hidden(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.42/4.47  tff(c_2880, plain, (![C_393, B_394]: (~r2_hidden(C_393, B_394) | ~r2_hidden(C_393, '#skF_4'))), inference(resolution, [status(thm)], [c_2873, c_12])).
% 11.42/4.47  tff(c_2909, plain, (~r2_hidden('#skF_10', '#skF_4')), inference(resolution, [status(thm)], [c_2191, c_2880])).
% 11.42/4.47  tff(c_2231, plain, (![A_291, B_292, C_293]: (r2_hidden(k1_mcart_1(A_291), B_292) | ~r2_hidden(A_291, k2_zfmisc_1(B_292, C_293)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_3061, plain, (![B_406, C_407]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_406, C_407))), B_406) | v1_xboole_0(k2_zfmisc_1(B_406, C_407)))), inference(resolution, [status(thm)], [c_4, c_2231])).
% 11.42/4.47  tff(c_3099, plain, (![B_408, C_409]: (~v1_xboole_0(B_408) | v1_xboole_0(k2_zfmisc_1(B_408, C_409)))), inference(resolution, [status(thm)], [c_3061, c_2])).
% 11.42/4.47  tff(c_131, plain, (![A_70]: (k1_xboole_0=A_70 | ~r1_tarski(A_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_109])).
% 11.42/4.47  tff(c_144, plain, (![A_64]: (k1_xboole_0=A_64 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_107, c_131])).
% 11.42/4.47  tff(c_2624, plain, (![A_64]: (A_64='#skF_4' | ~v1_xboole_0(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_2621, c_144])).
% 11.42/4.47  tff(c_3117, plain, (![B_410, C_411]: (k2_zfmisc_1(B_410, C_411)='#skF_4' | ~v1_xboole_0(B_410))), inference(resolution, [status(thm)], [c_3099, c_2624])).
% 11.42/4.47  tff(c_3128, plain, (![C_411]: (k2_zfmisc_1('#skF_4', C_411)='#skF_4')), inference(resolution, [status(thm)], [c_2623, c_3117])).
% 11.42/4.47  tff(c_3129, plain, (![C_412]: (k2_zfmisc_1('#skF_4', C_412)='#skF_4')), inference(resolution, [status(thm)], [c_2623, c_3117])).
% 11.42/4.47  tff(c_3155, plain, (![C_412, C_27]: (k3_zfmisc_1('#skF_4', C_412, C_27)=k2_zfmisc_1('#skF_4', C_27))), inference(superposition, [status(thm), theory('equality')], [c_3129, c_34])).
% 11.42/4.47  tff(c_3170, plain, (![C_412, C_27]: (k3_zfmisc_1('#skF_4', C_412, C_27)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3128, c_3155])).
% 11.42/4.47  tff(c_3174, plain, (r2_hidden('#skF_10', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3170, c_2191])).
% 11.42/4.47  tff(c_3180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2909, c_3174])).
% 11.42/4.47  tff(c_3182, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_2603])).
% 11.42/4.47  tff(c_3302, plain, (![A_429, B_430, C_431, D_432]: (k6_mcart_1(A_429, B_430, C_431, D_432)=k2_mcart_1(k1_mcart_1(D_432)) | ~m1_subset_1(D_432, k3_zfmisc_1(A_429, B_430, C_431)) | k1_xboole_0=C_431 | k1_xboole_0=B_430 | k1_xboole_0=A_429)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_3305, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_3302])).
% 11.42/4.47  tff(c_3308, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3182, c_3305])).
% 11.42/4.47  tff(c_3411, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3308])).
% 11.42/4.47  tff(c_3417, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3411, c_2497])).
% 11.42/4.47  tff(c_3422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_3417])).
% 11.42/4.47  tff(c_3424, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_3308])).
% 11.42/4.47  tff(c_3213, plain, (![A_420, B_421, C_422, D_423]: (k5_mcart_1(A_420, B_421, C_422, D_423)=k1_mcart_1(k1_mcart_1(D_423)) | ~m1_subset_1(D_423, k3_zfmisc_1(A_420, B_421, C_422)) | k1_xboole_0=C_422 | k1_xboole_0=B_421 | k1_xboole_0=A_420)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_3216, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_3213])).
% 11.42/4.47  tff(c_3219, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3182, c_3216])).
% 11.42/4.47  tff(c_3479, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_3424, c_3219])).
% 11.42/4.47  tff(c_3480, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_3479])).
% 11.42/4.47  tff(c_2265, plain, (![A_297, C_298, B_299]: (r2_hidden(k2_mcart_1(A_297), C_298) | ~r2_hidden(A_297, k2_zfmisc_1(B_299, C_298)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_2528, plain, (![A_339, C_340, A_341, B_342]: (r2_hidden(k2_mcart_1(A_339), C_340) | ~r2_hidden(A_339, k3_zfmisc_1(A_341, B_342, C_340)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2265])).
% 11.42/4.47  tff(c_2547, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_2191, c_2528])).
% 11.42/4.47  tff(c_2559, plain, (![B_343]: (r2_hidden(k2_mcart_1('#skF_10'), B_343) | ~r1_tarski('#skF_9', B_343))), inference(resolution, [status(thm)], [c_2547, c_6])).
% 11.42/4.47  tff(c_3220, plain, (![B_424, B_425]: (r2_hidden(k2_mcart_1('#skF_10'), B_424) | ~r1_tarski(B_425, B_424) | ~r1_tarski('#skF_9', B_425))), inference(resolution, [status(thm)], [c_2559, c_6])).
% 11.42/4.47  tff(c_3226, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_6') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_86, c_3220])).
% 11.42/4.47  tff(c_3235, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_3226])).
% 11.42/4.47  tff(c_3246, plain, (![B_6]: (r2_hidden(k2_mcart_1('#skF_10'), B_6) | ~r1_tarski('#skF_6', B_6))), inference(resolution, [status(thm)], [c_3235, c_6])).
% 11.42/4.47  tff(c_3359, plain, (![A_445, B_446, B_447]: (r2_hidden('#skF_3'(A_445, B_446), B_447) | ~r1_tarski(A_445, B_447) | r1_xboole_0(A_445, B_446))), inference(resolution, [status(thm)], [c_16, c_2284])).
% 11.42/4.47  tff(c_3384, plain, (![B_448, A_449, B_450]: (~v1_xboole_0(B_448) | ~r1_tarski(A_449, B_448) | r1_xboole_0(A_449, B_450))), inference(resolution, [status(thm)], [c_3359, c_2])).
% 11.42/4.47  tff(c_3399, plain, (![A_17, B_450]: (~v1_xboole_0(A_17) | r1_xboole_0(k1_xboole_0, B_450))), inference(resolution, [status(thm)], [c_24, c_3384])).
% 11.42/4.47  tff(c_3400, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_3399])).
% 11.42/4.47  tff(c_3409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3400, c_2497])).
% 11.42/4.47  tff(c_3425, plain, (![B_451]: (r1_xboole_0(k1_xboole_0, B_451))), inference(splitRight, [status(thm)], [c_3399])).
% 11.42/4.47  tff(c_3432, plain, (![C_452, B_453]: (~r2_hidden(C_452, B_453) | ~r2_hidden(C_452, k1_xboole_0))), inference(resolution, [status(thm)], [c_3425, c_12])).
% 11.42/4.47  tff(c_3459, plain, (~r2_hidden(k2_mcart_1('#skF_10'), k1_xboole_0)), inference(resolution, [status(thm)], [c_2547, c_3432])).
% 11.42/4.47  tff(c_3473, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_3246, c_3459])).
% 11.42/4.47  tff(c_3481, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3480, c_3473])).
% 11.42/4.47  tff(c_3498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_3481])).
% 11.42/4.47  tff(c_3499, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_3479])).
% 11.42/4.47  tff(c_2248, plain, (![A_294, B_295, C_296]: (k2_zfmisc_1(k2_zfmisc_1(A_294, B_295), C_296)=k3_zfmisc_1(A_294, B_295, C_296))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.42/4.47  tff(c_4571, plain, (![A_546, A_547, B_548, C_549]: (r2_hidden(k1_mcart_1(A_546), k2_zfmisc_1(A_547, B_548)) | ~r2_hidden(A_546, k3_zfmisc_1(A_547, B_548, C_549)))), inference(superposition, [status(thm), theory('equality')], [c_2248, c_38])).
% 11.42/4.47  tff(c_4631, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_2191, c_4571])).
% 11.42/4.47  tff(c_4641, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_4')), inference(resolution, [status(thm)], [c_4631, c_38])).
% 11.42/4.47  tff(c_4649, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3499, c_4641])).
% 11.42/4.47  tff(c_4651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2188, c_4649])).
% 11.42/4.47  tff(c_4652, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_124])).
% 11.42/4.47  tff(c_4654, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4652, c_96])).
% 11.42/4.47  tff(c_4674, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_123])).
% 11.42/4.47  tff(c_4678, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_107, c_4674])).
% 11.42/4.47  tff(c_4656, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4652, c_50])).
% 11.42/4.47  tff(c_5018, plain, (![A_606, B_607, C_608, D_609]: (k7_mcart_1(A_606, B_607, C_608, D_609)=k2_mcart_1(D_609) | ~m1_subset_1(D_609, k3_zfmisc_1(A_606, B_607, C_608)) | k1_xboole_0=C_608 | k1_xboole_0=B_607 | k1_xboole_0=A_606)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_5022, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4656, c_5018])).
% 11.42/4.47  tff(c_5063, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5022])).
% 11.42/4.47  tff(c_4786, plain, (![C_569, B_570, A_571]: (r2_hidden(C_569, B_570) | ~r2_hidden(C_569, A_571) | ~r1_tarski(A_571, B_570))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.47  tff(c_4814, plain, (![A_573, B_574]: (r2_hidden('#skF_1'(A_573), B_574) | ~r1_tarski(A_573, B_574) | v1_xboole_0(A_573))), inference(resolution, [status(thm)], [c_4, c_4786])).
% 11.42/4.47  tff(c_4835, plain, (![B_575, A_576]: (~v1_xboole_0(B_575) | ~r1_tarski(A_576, B_575) | v1_xboole_0(A_576))), inference(resolution, [status(thm)], [c_4814, c_2])).
% 11.42/4.47  tff(c_4855, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_4835])).
% 11.42/4.47  tff(c_4866, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_4855])).
% 11.42/4.47  tff(c_4912, plain, (![A_586, B_587, C_588]: (~r1_xboole_0(A_586, B_587) | ~r1_tarski(C_588, B_587) | ~r1_tarski(C_588, A_586))), inference(negUnitSimplification, [status(thm)], [c_4866, c_26])).
% 11.42/4.47  tff(c_4964, plain, (![C_599, B_600, A_601]: (~r1_tarski(C_599, B_600) | ~r1_tarski(C_599, k4_xboole_0(A_601, B_600)))), inference(resolution, [status(thm)], [c_28, c_4912])).
% 11.42/4.47  tff(c_4972, plain, (![B_600]: (~r1_tarski(k1_xboole_0, B_600))), inference(resolution, [status(thm)], [c_24, c_4964])).
% 11.42/4.47  tff(c_4977, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_4972])).
% 11.42/4.47  tff(c_4978, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_4855])).
% 11.42/4.47  tff(c_5065, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5063, c_4978])).
% 11.42/4.47  tff(c_5070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4678, c_5065])).
% 11.42/4.47  tff(c_5072, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_5022])).
% 11.42/4.47  tff(c_5166, plain, (![A_631, B_632, C_633, D_634]: (k6_mcart_1(A_631, B_632, C_633, D_634)=k2_mcart_1(k1_mcart_1(D_634)) | ~m1_subset_1(D_634, k3_zfmisc_1(A_631, B_632, C_633)) | k1_xboole_0=C_633 | k1_xboole_0=B_632 | k1_xboole_0=A_631)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_5169, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4656, c_5166])).
% 11.42/4.47  tff(c_5172, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_5072, c_5169])).
% 11.42/4.47  tff(c_5787, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_5172])).
% 11.42/4.47  tff(c_4748, plain, (![A_563, C_564, B_565]: (r2_hidden(k2_mcart_1(A_563), C_564) | ~r2_hidden(A_563, k2_zfmisc_1(B_565, C_564)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_5256, plain, (![B_647, C_648]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_647, C_648))), C_648) | v1_xboole_0(k2_zfmisc_1(B_647, C_648)))), inference(resolution, [status(thm)], [c_4, c_4748])).
% 11.42/4.47  tff(c_5285, plain, (![C_649, B_650]: (~v1_xboole_0(C_649) | v1_xboole_0(k2_zfmisc_1(B_650, C_649)))), inference(resolution, [status(thm)], [c_5256, c_2])).
% 11.42/4.47  tff(c_5296, plain, (![B_651, C_652]: (k2_zfmisc_1(B_651, C_652)=k1_xboole_0 | ~v1_xboole_0(C_652))), inference(resolution, [status(thm)], [c_5285, c_144])).
% 11.42/4.47  tff(c_5303, plain, (![B_653]: (k2_zfmisc_1(B_653, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4978, c_5296])).
% 11.42/4.47  tff(c_5398, plain, (![A_664]: (r2_hidden(k2_mcart_1(A_664), k1_xboole_0) | ~r2_hidden(A_664, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5303, c_36])).
% 11.42/4.47  tff(c_5409, plain, (![A_664]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_664, k1_xboole_0))), inference(resolution, [status(thm)], [c_5398, c_2])).
% 11.42/4.47  tff(c_5417, plain, (![A_664]: (~r2_hidden(A_664, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4978, c_5409])).
% 11.42/4.47  tff(c_5797, plain, (![A_664]: (~r2_hidden(A_664, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5787, c_5417])).
% 11.42/4.47  tff(c_5302, plain, (![B_651]: (k2_zfmisc_1(B_651, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4978, c_5296])).
% 11.42/4.47  tff(c_5800, plain, (![B_651]: (k2_zfmisc_1(B_651, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5787, c_5787, c_5302])).
% 11.42/4.47  tff(c_4767, plain, (![A_566, B_567, C_568]: (r2_hidden(k1_mcart_1(A_566), B_567) | ~r2_hidden(A_566, k2_zfmisc_1(B_567, C_568)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_6207, plain, (![A_724, A_725, B_726, C_727]: (r2_hidden(k1_mcart_1(A_724), k2_zfmisc_1(A_725, B_726)) | ~r2_hidden(A_724, k3_zfmisc_1(A_725, B_726, C_727)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4767])).
% 11.42/4.47  tff(c_6248, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_48, c_6207])).
% 11.42/4.47  tff(c_6267, plain, (r2_hidden(k1_mcart_1('#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5800, c_6248])).
% 11.42/4.47  tff(c_6269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5797, c_6267])).
% 11.42/4.47  tff(c_6271, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_5172])).
% 11.42/4.47  tff(c_5090, plain, (![A_617, B_618, C_619, D_620]: (k5_mcart_1(A_617, B_618, C_619, D_620)=k1_mcart_1(k1_mcart_1(D_620)) | ~m1_subset_1(D_620, k3_zfmisc_1(A_617, B_618, C_619)) | k1_xboole_0=C_619 | k1_xboole_0=B_618 | k1_xboole_0=A_617)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_5093, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4656, c_5090])).
% 11.42/4.47  tff(c_5096, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_5072, c_5093])).
% 11.42/4.47  tff(c_6277, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_6271, c_5096])).
% 11.42/4.47  tff(c_6278, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_6277])).
% 11.42/4.47  tff(c_4987, plain, (![A_602, C_603, A_604, B_605]: (r2_hidden(k2_mcart_1(A_602), C_603) | ~r2_hidden(A_602, k3_zfmisc_1(A_604, B_605, C_603)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4748])).
% 11.42/4.47  tff(c_5009, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_48, c_4987])).
% 11.42/4.47  tff(c_5023, plain, (![B_610]: (r2_hidden(k2_mcart_1('#skF_10'), B_610) | ~r1_tarski('#skF_9', B_610))), inference(resolution, [status(thm)], [c_5009, c_6])).
% 11.42/4.47  tff(c_5127, plain, (![B_628, B_629]: (r2_hidden(k2_mcart_1('#skF_10'), B_628) | ~r1_tarski(B_629, B_628) | ~r1_tarski('#skF_9', B_629))), inference(resolution, [status(thm)], [c_5023, c_6])).
% 11.42/4.47  tff(c_5133, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_6') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_86, c_5127])).
% 11.42/4.47  tff(c_5142, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_5133])).
% 11.42/4.47  tff(c_5153, plain, (![B_6]: (r2_hidden(k2_mcart_1('#skF_10'), B_6) | ~r1_tarski('#skF_6', B_6))), inference(resolution, [status(thm)], [c_5142, c_6])).
% 11.42/4.47  tff(c_5444, plain, (![A_668]: (~r2_hidden(A_668, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4978, c_5409])).
% 11.42/4.47  tff(c_5484, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_5153, c_5444])).
% 11.42/4.47  tff(c_6288, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6278, c_5484])).
% 11.42/4.47  tff(c_6305, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_6288])).
% 11.42/4.47  tff(c_6306, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_6277])).
% 11.42/4.47  tff(c_7279, plain, (![A_787, A_788, B_789, C_790]: (r2_hidden(k1_mcart_1(A_787), k2_zfmisc_1(A_788, B_789)) | ~r2_hidden(A_787, k3_zfmisc_1(A_788, B_789, C_790)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4767])).
% 11.42/4.47  tff(c_7344, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_48, c_7279])).
% 11.42/4.47  tff(c_7349, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_7')), inference(resolution, [status(thm)], [c_7344, c_38])).
% 11.42/4.47  tff(c_7357, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6306, c_7349])).
% 11.42/4.47  tff(c_7359, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4654, c_7357])).
% 11.42/4.47  tff(c_7360, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_123])).
% 11.42/4.47  tff(c_7416, plain, (~r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7360, c_4654])).
% 11.42/4.47  tff(c_7364, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_7360, c_48])).
% 11.42/4.47  tff(c_7682, plain, (![A_843, B_844, C_845, D_846]: (k7_mcart_1(A_843, B_844, C_845, D_846)=k2_mcart_1(D_846) | ~m1_subset_1(D_846, k3_zfmisc_1(A_843, B_844, C_845)) | k1_xboole_0=C_845 | k1_xboole_0=B_844 | k1_xboole_0=A_843)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_7686, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4656, c_7682])).
% 11.42/4.47  tff(c_7780, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_7686])).
% 11.42/4.47  tff(c_7786, plain, (![A_17]: (r1_tarski('#skF_4', A_17))), inference(demodulation, [status(thm), theory('equality')], [c_7780, c_24])).
% 11.42/4.47  tff(c_7883, plain, (![A_880, B_881, B_882]: (r2_hidden('#skF_3'(A_880, B_881), B_882) | ~r1_tarski(A_880, B_882) | r1_xboole_0(A_880, B_881))), inference(resolution, [status(thm)], [c_16, c_7400])).
% 11.42/4.47  tff(c_7908, plain, (![B_883, A_884, B_885]: (~v1_xboole_0(B_883) | ~r1_tarski(A_884, B_883) | r1_xboole_0(A_884, B_885))), inference(resolution, [status(thm)], [c_7883, c_2])).
% 11.42/4.47  tff(c_7917, plain, (![A_17, B_885]: (~v1_xboole_0(A_17) | r1_xboole_0('#skF_4', B_885))), inference(resolution, [status(thm)], [c_7786, c_7908])).
% 11.42/4.47  tff(c_7921, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_7917])).
% 11.42/4.47  tff(c_7783, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7780, c_7673])).
% 11.42/4.47  tff(c_7930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7921, c_7783])).
% 11.42/4.47  tff(c_7947, plain, (![B_888]: (r1_xboole_0('#skF_4', B_888))), inference(splitRight, [status(thm)], [c_7917])).
% 11.42/4.47  tff(c_7969, plain, (![C_890, B_891]: (~r2_hidden(C_890, B_891) | ~r2_hidden(C_890, '#skF_4'))), inference(resolution, [status(thm)], [c_7947, c_12])).
% 11.42/4.47  tff(c_7995, plain, (~r2_hidden('#skF_10', '#skF_4')), inference(resolution, [status(thm)], [c_7364, c_7969])).
% 11.42/4.47  tff(c_7463, plain, (![A_805, B_806, C_807]: (r2_hidden(k1_mcart_1(A_805), B_806) | ~r2_hidden(A_805, k2_zfmisc_1(B_806, C_807)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_8253, plain, (![B_917, C_918]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_917, C_918))), B_917) | v1_xboole_0(k2_zfmisc_1(B_917, C_918)))), inference(resolution, [status(thm)], [c_4, c_7463])).
% 11.42/4.47  tff(c_8291, plain, (![B_919, C_920]: (~v1_xboole_0(B_919) | v1_xboole_0(k2_zfmisc_1(B_919, C_920)))), inference(resolution, [status(thm)], [c_8253, c_2])).
% 11.42/4.47  tff(c_7784, plain, (![A_64]: (A_64='#skF_4' | ~v1_xboole_0(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_7780, c_144])).
% 11.42/4.47  tff(c_8312, plain, (![B_921, C_922]: (k2_zfmisc_1(B_921, C_922)='#skF_4' | ~v1_xboole_0(B_921))), inference(resolution, [status(thm)], [c_8291, c_7784])).
% 11.42/4.47  tff(c_8326, plain, (![C_922]: (k2_zfmisc_1('#skF_4', C_922)='#skF_4')), inference(resolution, [status(thm)], [c_7783, c_8312])).
% 11.42/4.47  tff(c_8327, plain, (![C_923]: (k2_zfmisc_1('#skF_4', C_923)='#skF_4')), inference(resolution, [status(thm)], [c_7783, c_8312])).
% 11.42/4.47  tff(c_8353, plain, (![C_923, C_27]: (k3_zfmisc_1('#skF_4', C_923, C_27)=k2_zfmisc_1('#skF_4', C_27))), inference(superposition, [status(thm), theory('equality')], [c_8327, c_34])).
% 11.42/4.47  tff(c_8368, plain, (![C_923, C_27]: (k3_zfmisc_1('#skF_4', C_923, C_27)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8326, c_8353])).
% 11.42/4.47  tff(c_8377, plain, (r2_hidden('#skF_10', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8368, c_7364])).
% 11.42/4.47  tff(c_8383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7995, c_8377])).
% 11.42/4.47  tff(c_8385, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_7686])).
% 11.42/4.47  tff(c_7758, plain, (![A_853, B_854, C_855, D_856]: (k5_mcart_1(A_853, B_854, C_855, D_856)=k1_mcart_1(k1_mcart_1(D_856)) | ~m1_subset_1(D_856, k3_zfmisc_1(A_853, B_854, C_855)) | k1_xboole_0=C_855 | k1_xboole_0=B_854 | k1_xboole_0=A_853)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_7762, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4656, c_7758])).
% 11.42/4.47  tff(c_8452, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_8385, c_7762])).
% 11.42/4.47  tff(c_8453, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_8452])).
% 11.42/4.47  tff(c_8458, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8453, c_7673])).
% 11.42/4.47  tff(c_7417, plain, (![A_798, C_799, B_800]: (r2_hidden(k2_mcart_1(A_798), C_799) | ~r2_hidden(A_798, k2_zfmisc_1(B_800, C_799)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_8498, plain, (![B_945, C_946]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_945, C_946))), C_946) | v1_xboole_0(k2_zfmisc_1(B_945, C_946)))), inference(resolution, [status(thm)], [c_4, c_7417])).
% 11.42/4.47  tff(c_8561, plain, (![C_949, B_950]: (~v1_xboole_0(C_949) | v1_xboole_0(k2_zfmisc_1(B_950, C_949)))), inference(resolution, [status(thm)], [c_8498, c_2])).
% 11.42/4.47  tff(c_8459, plain, (![A_64]: (A_64='#skF_8' | ~v1_xboole_0(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_8453, c_144])).
% 11.42/4.47  tff(c_8572, plain, (![B_951, C_952]: (k2_zfmisc_1(B_951, C_952)='#skF_8' | ~v1_xboole_0(C_952))), inference(resolution, [status(thm)], [c_8561, c_8459])).
% 11.42/4.47  tff(c_8609, plain, (![B_956]: (k2_zfmisc_1(B_956, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_8458, c_8572])).
% 11.42/4.47  tff(c_8692, plain, (![A_965]: (r2_hidden(k2_mcart_1(A_965), '#skF_8') | ~r2_hidden(A_965, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8609, c_36])).
% 11.42/4.47  tff(c_8700, plain, (![A_965]: (~v1_xboole_0('#skF_8') | ~r2_hidden(A_965, '#skF_8'))), inference(resolution, [status(thm)], [c_8692, c_2])).
% 11.42/4.47  tff(c_8707, plain, (![A_965]: (~r2_hidden(A_965, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_8458, c_8700])).
% 11.42/4.47  tff(c_8525, plain, (![C_946, B_945]: (~v1_xboole_0(C_946) | v1_xboole_0(k2_zfmisc_1(B_945, C_946)))), inference(resolution, [status(thm)], [c_8498, c_2])).
% 11.42/4.47  tff(c_8885, plain, (![B_979, C_980]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_979, C_980))), B_979) | v1_xboole_0(k2_zfmisc_1(B_979, C_980)))), inference(resolution, [status(thm)], [c_4, c_7463])).
% 11.42/4.47  tff(c_9018, plain, (![B_988, C_989]: (~v1_xboole_0(B_988) | v1_xboole_0(k2_zfmisc_1(B_988, C_989)))), inference(resolution, [status(thm)], [c_8885, c_2])).
% 11.42/4.47  tff(c_9044, plain, (![B_990, C_991]: (k2_zfmisc_1(B_990, C_991)='#skF_8' | ~v1_xboole_0(B_990))), inference(resolution, [status(thm)], [c_9018, c_8459])).
% 11.42/4.47  tff(c_9050, plain, (![B_945, C_946, C_991]: (k2_zfmisc_1(k2_zfmisc_1(B_945, C_946), C_991)='#skF_8' | ~v1_xboole_0(C_946))), inference(resolution, [status(thm)], [c_8525, c_9044])).
% 11.42/4.47  tff(c_9113, plain, (![B_1000, C_1001, C_1002]: (k3_zfmisc_1(B_1000, C_1001, C_1002)='#skF_8' | ~v1_xboole_0(C_1001))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_9050])).
% 11.42/4.47  tff(c_9125, plain, (![B_1000, C_1002]: (k3_zfmisc_1(B_1000, '#skF_8', C_1002)='#skF_8')), inference(resolution, [status(thm)], [c_8458, c_9113])).
% 11.42/4.47  tff(c_9127, plain, (r2_hidden('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9125, c_7364])).
% 11.42/4.47  tff(c_9133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8707, c_9127])).
% 11.42/4.47  tff(c_9135, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_8452])).
% 11.42/4.47  tff(c_8416, plain, (![A_933, B_934, C_935, D_936]: (k6_mcart_1(A_933, B_934, C_935, D_936)=k2_mcart_1(k1_mcart_1(D_936)) | ~m1_subset_1(D_936, k3_zfmisc_1(A_933, B_934, C_935)) | k1_xboole_0=C_935 | k1_xboole_0=B_934 | k1_xboole_0=A_933)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_8419, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4656, c_8416])).
% 11.42/4.47  tff(c_8422, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_8385, c_8419])).
% 11.42/4.47  tff(c_9409, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_9135, c_8422])).
% 11.42/4.47  tff(c_9410, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_9409])).
% 11.42/4.47  tff(c_7434, plain, (![A_801, B_802, C_803]: (k2_zfmisc_1(k2_zfmisc_1(A_801, B_802), C_803)=k3_zfmisc_1(A_801, B_802, C_803))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.42/4.47  tff(c_7687, plain, (![A_847, C_848, A_849, B_850]: (r2_hidden(k2_mcart_1(A_847), C_848) | ~r2_hidden(A_847, k3_zfmisc_1(A_849, B_850, C_848)))), inference(superposition, [status(thm), theory('equality')], [c_7434, c_36])).
% 11.42/4.47  tff(c_7706, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_7364, c_7687])).
% 11.42/4.47  tff(c_7718, plain, (![B_851]: (r2_hidden(k2_mcart_1('#skF_10'), B_851) | ~r1_tarski('#skF_9', B_851))), inference(resolution, [status(thm)], [c_7706, c_6])).
% 11.42/4.47  tff(c_8437, plain, (![B_941, B_942]: (r2_hidden(k2_mcart_1('#skF_10'), B_941) | ~r1_tarski(B_942, B_941) | ~r1_tarski('#skF_9', B_942))), inference(resolution, [status(thm)], [c_7718, c_6])).
% 11.42/4.47  tff(c_8451, plain, (![A_17]: (r2_hidden(k2_mcart_1('#skF_10'), A_17) | ~r1_tarski('#skF_9', k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_8437])).
% 11.42/4.47  tff(c_9151, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_8451])).
% 11.42/4.47  tff(c_9418, plain, (~r1_tarski('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9410, c_9151])).
% 11.42/4.47  tff(c_9430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_9418])).
% 11.42/4.47  tff(c_9432, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_9409])).
% 11.42/4.47  tff(c_9134, plain, (k1_xboole_0='#skF_6' | k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_8452])).
% 11.42/4.47  tff(c_9512, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_9432, c_9134])).
% 11.42/4.47  tff(c_10273, plain, (![A_1102, A_1103, B_1104, C_1105]: (r2_hidden(k1_mcart_1(A_1102), k2_zfmisc_1(A_1103, B_1104)) | ~r2_hidden(A_1102, k3_zfmisc_1(A_1103, B_1104, C_1105)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_7463])).
% 11.42/4.47  tff(c_10333, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_7364, c_10273])).
% 11.42/4.47  tff(c_10339, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), '#skF_4')), inference(resolution, [status(thm)], [c_10333, c_38])).
% 11.42/4.47  tff(c_10348, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9512, c_10339])).
% 11.42/4.47  tff(c_10350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7416, c_10348])).
% 11.42/4.47  tff(c_10352, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_8451])).
% 11.42/4.47  tff(c_7742, plain, (![B_851]: (~v1_xboole_0(B_851) | ~r1_tarski('#skF_9', B_851))), inference(resolution, [status(thm)], [c_7718, c_2])).
% 11.42/4.47  tff(c_10357, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_10352, c_7742])).
% 11.42/4.47  tff(c_10375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7673, c_10357])).
% 11.42/4.47  tff(c_10376, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8') | ~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_46])).
% 11.42/4.47  tff(c_10382, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_10376])).
% 11.42/4.47  tff(c_11082, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_11081, c_10382])).
% 11.42/4.47  tff(c_11085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10883, c_11082])).
% 11.42/4.47  tff(c_11086, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_10952])).
% 11.42/4.47  tff(c_11088, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_11086])).
% 11.42/4.47  tff(c_11094, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11088, c_10782])).
% 11.42/4.47  tff(c_11099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10444, c_11094])).
% 11.42/4.47  tff(c_11100, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_11086])).
% 11.42/4.47  tff(c_10897, plain, (![B_1189]: (r2_hidden(k2_mcart_1('#skF_10'), B_1189) | ~r1_tarski('#skF_9', B_1189))), inference(resolution, [status(thm)], [c_10883, c_6])).
% 11.42/4.47  tff(c_10984, plain, (![B_1204, B_1205]: (r2_hidden(k2_mcart_1('#skF_10'), B_1204) | ~r1_tarski(B_1205, B_1204) | ~r1_tarski('#skF_9', B_1205))), inference(resolution, [status(thm)], [c_10897, c_6])).
% 11.42/4.47  tff(c_11004, plain, (![A_17]: (r2_hidden(k2_mcart_1('#skF_10'), A_17) | ~r1_tarski('#skF_9', k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_10984])).
% 11.42/4.47  tff(c_11025, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11004])).
% 11.42/4.47  tff(c_11104, plain, (~r1_tarski('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11100, c_11025])).
% 11.42/4.47  tff(c_11114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_11104])).
% 11.42/4.47  tff(c_11116, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_11004])).
% 11.42/4.47  tff(c_10921, plain, (![B_1189]: (~v1_xboole_0(B_1189) | ~r1_tarski('#skF_9', B_1189))), inference(resolution, [status(thm)], [c_10897, c_2])).
% 11.42/4.47  tff(c_11128, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_11116, c_10921])).
% 11.42/4.47  tff(c_11146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10782, c_11128])).
% 11.42/4.47  tff(c_11147, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_10394])).
% 11.42/4.47  tff(c_11153, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_11147, c_48])).
% 11.42/4.47  tff(c_11299, plain, (![A_1241, C_1242, B_1243]: (r2_hidden(k2_mcart_1(A_1241), C_1242) | ~r2_hidden(A_1241, k2_zfmisc_1(B_1243, C_1242)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_11515, plain, (![A_1273, C_1274, A_1275, B_1276]: (r2_hidden(k2_mcart_1(A_1273), C_1274) | ~r2_hidden(A_1273, k3_zfmisc_1(A_1275, B_1276, C_1274)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_11299])).
% 11.42/4.47  tff(c_11535, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_11153, c_11515])).
% 11.42/4.47  tff(c_10377, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 11.42/4.47  tff(c_10381, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_10377, c_2])).
% 11.42/4.47  tff(c_11149, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11147, c_10381])).
% 11.42/4.47  tff(c_11539, plain, (![A_1277, B_1278, C_1279, D_1280]: (k7_mcart_1(A_1277, B_1278, C_1279, D_1280)=k2_mcart_1(D_1280) | ~m1_subset_1(D_1280, k3_zfmisc_1(A_1277, B_1278, C_1279)) | k1_xboole_0=C_1279 | k1_xboole_0=B_1278 | k1_xboole_0=A_1277)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_11543, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_11539])).
% 11.42/4.47  tff(c_11576, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_11543])).
% 11.42/4.47  tff(c_11203, plain, (![C_1225, B_1226, A_1227]: (r2_hidden(C_1225, B_1226) | ~r2_hidden(C_1225, A_1227) | ~r1_tarski(A_1227, B_1226))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.47  tff(c_11328, plain, (![A_1247, B_1248]: (r2_hidden('#skF_1'(A_1247), B_1248) | ~r1_tarski(A_1247, B_1248) | v1_xboole_0(A_1247))), inference(resolution, [status(thm)], [c_4, c_11203])).
% 11.42/4.47  tff(c_11349, plain, (![B_1249, A_1250]: (~v1_xboole_0(B_1249) | ~r1_tarski(A_1250, B_1249) | v1_xboole_0(A_1250))), inference(resolution, [status(thm)], [c_11328, c_2])).
% 11.42/4.47  tff(c_11369, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_11349])).
% 11.42/4.47  tff(c_11370, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_11369])).
% 11.42/4.47  tff(c_11437, plain, (![A_1258, B_1259, C_1260]: (~r1_xboole_0(A_1258, B_1259) | ~r1_tarski(C_1260, B_1259) | ~r1_tarski(C_1260, A_1258))), inference(negUnitSimplification, [status(thm)], [c_11370, c_26])).
% 11.42/4.47  tff(c_11492, plain, (![C_1270, B_1271, A_1272]: (~r1_tarski(C_1270, B_1271) | ~r1_tarski(C_1270, k4_xboole_0(A_1272, B_1271)))), inference(resolution, [status(thm)], [c_28, c_11437])).
% 11.42/4.47  tff(c_11500, plain, (![B_1271]: (~r1_tarski(k1_xboole_0, B_1271))), inference(resolution, [status(thm)], [c_24, c_11492])).
% 11.42/4.47  tff(c_11505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_11500])).
% 11.42/4.47  tff(c_11506, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_11369])).
% 11.42/4.47  tff(c_11578, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11576, c_11506])).
% 11.42/4.47  tff(c_11583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11149, c_11578])).
% 11.42/4.47  tff(c_11584, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_11543])).
% 11.42/4.47  tff(c_11649, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_11584])).
% 11.42/4.47  tff(c_11650, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_11649, c_10382])).
% 11.42/4.47  tff(c_11653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11535, c_11650])).
% 11.42/4.47  tff(c_11654, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_11584])).
% 11.42/4.47  tff(c_11656, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_11654])).
% 11.42/4.47  tff(c_11660, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11656, c_11506])).
% 11.42/4.47  tff(c_11665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10444, c_11660])).
% 11.42/4.47  tff(c_11666, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_11654])).
% 11.42/4.47  tff(c_11672, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11666, c_11506])).
% 11.42/4.47  tff(c_11677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10437, c_11672])).
% 11.42/4.47  tff(c_11678, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_10395])).
% 11.42/4.47  tff(c_11688, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_11678, c_50])).
% 11.42/4.47  tff(c_12048, plain, (![A_1354, B_1355, C_1356, D_1357]: (k7_mcart_1(A_1354, B_1355, C_1356, D_1357)=k2_mcart_1(D_1357) | ~m1_subset_1(D_1357, k3_zfmisc_1(A_1354, B_1355, C_1356)) | k1_xboole_0=C_1356 | k1_xboole_0=B_1355 | k1_xboole_0=A_1354)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_12052, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_11688, c_12048])).
% 11.42/4.47  tff(c_12092, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_12052])).
% 11.42/4.47  tff(c_12094, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12092, c_12039])).
% 11.42/4.47  tff(c_12099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11707, c_12094])).
% 11.42/4.47  tff(c_12100, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_6' | k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_12052])).
% 11.42/4.47  tff(c_12488, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_12100])).
% 11.42/4.47  tff(c_11685, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_11678, c_10382])).
% 11.42/4.47  tff(c_12496, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12488, c_11685])).
% 11.42/4.47  tff(c_12499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12128, c_12496])).
% 11.42/4.47  tff(c_12500, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_12100])).
% 11.42/4.47  tff(c_12509, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_12500])).
% 11.42/4.47  tff(c_12520, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12509, c_12039])).
% 11.42/4.47  tff(c_11781, plain, (![A_1313, B_1314, C_1315]: (r2_hidden(k1_mcart_1(A_1313), B_1314) | ~r2_hidden(A_1313, k2_zfmisc_1(B_1314, C_1315)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_12733, plain, (![B_1430, C_1431]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1430, C_1431))), B_1430) | v1_xboole_0(k2_zfmisc_1(B_1430, C_1431)))), inference(resolution, [status(thm)], [c_4, c_11781])).
% 11.42/4.47  tff(c_12775, plain, (![B_1432, C_1433]: (~v1_xboole_0(B_1432) | v1_xboole_0(k2_zfmisc_1(B_1432, C_1433)))), inference(resolution, [status(thm)], [c_12733, c_2])).
% 11.42/4.47  tff(c_10401, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_10383])).
% 11.42/4.47  tff(c_10438, plain, (![A_1111]: (k1_xboole_0=A_1111 | ~v1_xboole_0(A_1111))), inference(resolution, [status(thm)], [c_10427, c_10401])).
% 11.42/4.47  tff(c_12521, plain, (![A_1111]: (A_1111='#skF_8' | ~v1_xboole_0(A_1111))), inference(demodulation, [status(thm), theory('equality')], [c_12509, c_10438])).
% 11.42/4.47  tff(c_12843, plain, (![B_1436, C_1437]: (k2_zfmisc_1(B_1436, C_1437)='#skF_8' | ~v1_xboole_0(B_1436))), inference(resolution, [status(thm)], [c_12775, c_12521])).
% 11.42/4.47  tff(c_12854, plain, (![C_1437]: (k2_zfmisc_1('#skF_8', C_1437)='#skF_8')), inference(resolution, [status(thm)], [c_12520, c_12843])).
% 11.42/4.47  tff(c_12528, plain, (![B_1413, C_1414]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1413, C_1414))), C_1414) | v1_xboole_0(k2_zfmisc_1(B_1413, C_1414)))), inference(resolution, [status(thm)], [c_4, c_11800])).
% 11.42/4.47  tff(c_12673, plain, (![C_1426, B_1427]: (~v1_xboole_0(C_1426) | v1_xboole_0(k2_zfmisc_1(B_1427, C_1426)))), inference(resolution, [status(thm)], [c_12528, c_2])).
% 11.42/4.47  tff(c_12902, plain, (![B_1441, C_1442]: (k2_zfmisc_1(B_1441, C_1442)='#skF_8' | ~v1_xboole_0(C_1442))), inference(resolution, [status(thm)], [c_12673, c_12521])).
% 11.42/4.47  tff(c_12971, plain, (![B_1447]: (k2_zfmisc_1(B_1447, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_12520, c_12902])).
% 11.42/4.47  tff(c_12999, plain, (![B_1447, C_27]: (k3_zfmisc_1(B_1447, '#skF_8', C_27)=k2_zfmisc_1('#skF_8', C_27))), inference(superposition, [status(thm), theory('equality')], [c_12971, c_34])).
% 11.42/4.47  tff(c_13020, plain, (![B_1447, C_27]: (k3_zfmisc_1(B_1447, '#skF_8', C_27)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12854, c_12999])).
% 11.42/4.47  tff(c_70, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_48, c_2])).
% 11.42/4.47  tff(c_13025, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_13020, c_70])).
% 11.42/4.47  tff(c_13031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12520, c_13025])).
% 11.42/4.47  tff(c_13032, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_12500])).
% 11.42/4.47  tff(c_12144, plain, (![B_1372]: (r2_hidden(k2_mcart_1('#skF_10'), B_1372) | ~r1_tarski('#skF_9', B_1372))), inference(resolution, [status(thm)], [c_12128, c_6])).
% 11.42/4.47  tff(c_12221, plain, (![B_1387, B_1388]: (r2_hidden(k2_mcart_1('#skF_10'), B_1387) | ~r1_tarski(B_1388, B_1387) | ~r1_tarski('#skF_9', B_1388))), inference(resolution, [status(thm)], [c_12144, c_6])).
% 11.42/4.47  tff(c_12227, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_6') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_86, c_12221])).
% 11.42/4.47  tff(c_12236, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12227])).
% 11.42/4.47  tff(c_12247, plain, (![B_6]: (r2_hidden(k2_mcart_1('#skF_10'), B_6) | ~r1_tarski('#skF_6', B_6))), inference(resolution, [status(thm)], [c_12236, c_6])).
% 11.42/4.47  tff(c_14, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), B_11) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.42/4.47  tff(c_12303, plain, (![A_1392, B_1393, B_1394]: (r2_hidden('#skF_3'(A_1392, B_1393), B_1394) | ~r1_tarski(B_1393, B_1394) | r1_xboole_0(A_1392, B_1393))), inference(resolution, [status(thm)], [c_14, c_11708])).
% 11.42/4.47  tff(c_12328, plain, (![B_1395, B_1396, A_1397]: (~v1_xboole_0(B_1395) | ~r1_tarski(B_1396, B_1395) | r1_xboole_0(A_1397, B_1396))), inference(resolution, [status(thm)], [c_12303, c_2])).
% 11.42/4.47  tff(c_12343, plain, (![A_17, A_1397]: (~v1_xboole_0(A_17) | r1_xboole_0(A_1397, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_12328])).
% 11.42/4.47  tff(c_12344, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_12343])).
% 11.42/4.47  tff(c_12353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12344, c_12039])).
% 11.42/4.47  tff(c_12362, plain, (![A_1400]: (r1_xboole_0(A_1400, k1_xboole_0))), inference(splitRight, [status(thm)], [c_12343])).
% 11.42/4.47  tff(c_12369, plain, (![C_1401, A_1402]: (~r2_hidden(C_1401, k1_xboole_0) | ~r2_hidden(C_1401, A_1402))), inference(resolution, [status(thm)], [c_12362, c_12])).
% 11.42/4.47  tff(c_12398, plain, (![A_1402]: (~r2_hidden(k2_mcart_1('#skF_10'), A_1402) | ~r1_tarski('#skF_6', k1_xboole_0))), inference(resolution, [status(thm)], [c_12247, c_12369])).
% 11.42/4.47  tff(c_12409, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_12398])).
% 11.42/4.47  tff(c_13042, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13032, c_12409])).
% 11.42/4.47  tff(c_13056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_13042])).
% 11.42/4.47  tff(c_13058, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_12398])).
% 11.42/4.47  tff(c_12264, plain, (![B_1390]: (r2_hidden(k2_mcart_1('#skF_10'), B_1390) | ~r1_tarski('#skF_6', B_1390))), inference(resolution, [status(thm)], [c_12236, c_6])).
% 11.42/4.47  tff(c_12291, plain, (![B_1390]: (~v1_xboole_0(B_1390) | ~r1_tarski('#skF_6', B_1390))), inference(resolution, [status(thm)], [c_12264, c_2])).
% 11.42/4.47  tff(c_13063, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_13058, c_12291])).
% 11.42/4.47  tff(c_13083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12039, c_13063])).
% 11.42/4.47  tff(c_13084, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_10394])).
% 11.42/4.47  tff(c_13089, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_13084, c_48])).
% 11.42/4.47  tff(c_13183, plain, (![A_1464, B_1465, C_1466]: (k2_zfmisc_1(k2_zfmisc_1(A_1464, B_1465), C_1466)=k3_zfmisc_1(A_1464, B_1465, C_1466))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.42/4.47  tff(c_13426, plain, (![A_1500, C_1501, A_1502, B_1503]: (r2_hidden(k2_mcart_1(A_1500), C_1501) | ~r2_hidden(A_1500, k3_zfmisc_1(A_1502, B_1503, C_1501)))), inference(superposition, [status(thm), theory('equality')], [c_13183, c_36])).
% 11.42/4.47  tff(c_13445, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_13089, c_13426])).
% 11.42/4.47  tff(c_13086, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13084, c_10381])).
% 11.42/4.47  tff(c_13532, plain, (![A_1514, B_1515, C_1516, D_1517]: (k7_mcart_1(A_1514, B_1515, C_1516, D_1517)=k2_mcart_1(D_1517) | ~m1_subset_1(D_1517, k3_zfmisc_1(A_1514, B_1515, C_1516)) | k1_xboole_0=C_1516 | k1_xboole_0=B_1515 | k1_xboole_0=A_1514)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_13536, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_11688, c_13532])).
% 11.42/4.47  tff(c_13574, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_13536])).
% 11.42/4.47  tff(c_13097, plain, (![C_1451, B_1452, A_1453]: (r2_hidden(C_1451, B_1452) | ~r2_hidden(C_1451, A_1453) | ~r1_tarski(A_1453, B_1452))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.47  tff(c_13245, plain, (![A_1474, B_1475]: (r2_hidden('#skF_1'(A_1474), B_1475) | ~r1_tarski(A_1474, B_1475) | v1_xboole_0(A_1474))), inference(resolution, [status(thm)], [c_4, c_13097])).
% 11.42/4.47  tff(c_13266, plain, (![B_1476, A_1477]: (~v1_xboole_0(B_1476) | ~r1_tarski(A_1477, B_1476) | v1_xboole_0(A_1477))), inference(resolution, [status(thm)], [c_13245, c_2])).
% 11.42/4.47  tff(c_13282, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_13266])).
% 11.42/4.47  tff(c_13283, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_13282])).
% 11.42/4.47  tff(c_13306, plain, (![A_1480, B_1481, C_1482]: (~r1_xboole_0(A_1480, B_1481) | ~r1_tarski(C_1482, B_1481) | ~r1_tarski(C_1482, A_1480))), inference(negUnitSimplification, [status(thm)], [c_13283, c_26])).
% 11.42/4.47  tff(c_13393, plain, (![C_1494, B_1495, A_1496]: (~r1_tarski(C_1494, B_1495) | ~r1_tarski(C_1494, k4_xboole_0(A_1496, B_1495)))), inference(resolution, [status(thm)], [c_28, c_13306])).
% 11.42/4.47  tff(c_13401, plain, (![B_1495]: (~r1_tarski(k1_xboole_0, B_1495))), inference(resolution, [status(thm)], [c_24, c_13393])).
% 11.42/4.47  tff(c_13406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_13401])).
% 11.42/4.47  tff(c_13407, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_13282])).
% 11.42/4.47  tff(c_13576, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13574, c_13407])).
% 11.42/4.47  tff(c_13581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13086, c_13576])).
% 11.42/4.47  tff(c_13582, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_6' | k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_13536])).
% 11.42/4.47  tff(c_13646, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_13582])).
% 11.42/4.47  tff(c_13647, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_13646, c_11685])).
% 11.42/4.47  tff(c_13650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13445, c_13647])).
% 11.42/4.47  tff(c_13651, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_13582])).
% 11.42/4.47  tff(c_13653, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_13651])).
% 11.42/4.47  tff(c_13657, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_13653, c_13407])).
% 11.42/4.47  tff(c_13166, plain, (![A_1461, C_1462, B_1463]: (r2_hidden(k2_mcart_1(A_1461), C_1462) | ~r2_hidden(A_1461, k2_zfmisc_1(B_1463, C_1462)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_13727, plain, (![B_1542, C_1543]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1542, C_1543))), C_1543) | v1_xboole_0(k2_zfmisc_1(B_1542, C_1543)))), inference(resolution, [status(thm)], [c_4, c_13166])).
% 11.42/4.47  tff(c_13760, plain, (![C_1544, B_1545]: (~v1_xboole_0(C_1544) | v1_xboole_0(k2_zfmisc_1(B_1545, C_1544)))), inference(resolution, [status(thm)], [c_13727, c_2])).
% 11.42/4.47  tff(c_13658, plain, (![A_1111]: (A_1111='#skF_8' | ~v1_xboole_0(A_1111))), inference(demodulation, [status(thm), theory('equality')], [c_13653, c_10438])).
% 11.42/4.47  tff(c_13771, plain, (![B_1546, C_1547]: (k2_zfmisc_1(B_1546, C_1547)='#skF_8' | ~v1_xboole_0(C_1547))), inference(resolution, [status(thm)], [c_13760, c_13658])).
% 11.42/4.47  tff(c_13806, plain, (![B_1549]: (k2_zfmisc_1(B_1549, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_13657, c_13771])).
% 11.42/4.47  tff(c_13927, plain, (![A_1562, B_1563]: (r2_hidden(k1_mcart_1(A_1562), B_1563) | ~r2_hidden(A_1562, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_13806, c_38])).
% 11.42/4.47  tff(c_13951, plain, (![B_1563, A_1562]: (~v1_xboole_0(B_1563) | ~r2_hidden(A_1562, '#skF_8'))), inference(resolution, [status(thm)], [c_13927, c_2])).
% 11.42/4.47  tff(c_13952, plain, (![A_1562]: (~r2_hidden(A_1562, '#skF_8'))), inference(splitLeft, [status(thm)], [c_13951])).
% 11.42/4.47  tff(c_13821, plain, (![B_1549, C_27]: (k3_zfmisc_1(B_1549, '#skF_8', C_27)=k2_zfmisc_1('#skF_8', C_27))), inference(superposition, [status(thm), theory('equality')], [c_13806, c_34])).
% 11.42/4.47  tff(c_14107, plain, (r2_hidden('#skF_10', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_13821, c_13089])).
% 11.42/4.47  tff(c_14147, plain, (r2_hidden(k1_mcart_1('#skF_10'), '#skF_8')), inference(resolution, [status(thm)], [c_14107, c_38])).
% 11.42/4.47  tff(c_14158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13952, c_14147])).
% 11.42/4.47  tff(c_14159, plain, (![B_1563]: (~v1_xboole_0(B_1563))), inference(splitRight, [status(thm)], [c_13951])).
% 11.42/4.47  tff(c_14171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14159, c_13657])).
% 11.42/4.47  tff(c_14172, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_13651])).
% 11.42/4.47  tff(c_14177, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14172, c_13407])).
% 11.42/4.47  tff(c_14182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10437, c_14177])).
% 11.42/4.47  tff(c_14183, plain, ('#skF_6'='#skF_9'), inference(splitRight, [status(thm)], [c_10396])).
% 11.42/4.47  tff(c_14199, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_14183, c_50])).
% 11.42/4.47  tff(c_14757, plain, (![A_1665, B_1666, C_1667, D_1668]: (k7_mcart_1(A_1665, B_1666, C_1667, D_1668)=k2_mcart_1(D_1668) | ~m1_subset_1(D_1668, k3_zfmisc_1(A_1665, B_1666, C_1667)) | k1_xboole_0=C_1667 | k1_xboole_0=B_1666 | k1_xboole_0=A_1665)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_14761, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_14199, c_14757])).
% 11.42/4.47  tff(c_14768, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_14761])).
% 11.42/4.47  tff(c_14770, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14768, c_14563])).
% 11.42/4.47  tff(c_14775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14237, c_14770])).
% 11.42/4.47  tff(c_14776, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_9' | k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_14761])).
% 11.42/4.47  tff(c_14949, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_14776])).
% 11.42/4.47  tff(c_14196, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14183, c_10382])).
% 11.42/4.47  tff(c_14950, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14949, c_14196])).
% 11.42/4.47  tff(c_14953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14594, c_14950])).
% 11.42/4.47  tff(c_14954, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_14776])).
% 11.42/4.47  tff(c_14956, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_14954])).
% 11.42/4.47  tff(c_14966, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14956, c_14563])).
% 11.42/4.47  tff(c_14971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14226, c_14966])).
% 11.42/4.47  tff(c_14972, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_14954])).
% 11.42/4.47  tff(c_14603, plain, (![B_1644]: (r2_hidden(k2_mcart_1('#skF_10'), B_1644) | ~r1_tarski('#skF_9', B_1644))), inference(resolution, [status(thm)], [c_14594, c_6])).
% 11.42/4.47  tff(c_14736, plain, (![B_1663, B_1664]: (r2_hidden(k2_mcart_1('#skF_10'), B_1663) | ~r1_tarski(B_1664, B_1663) | ~r1_tarski('#skF_9', B_1664))), inference(resolution, [status(thm)], [c_14603, c_6])).
% 11.42/4.47  tff(c_14751, plain, (![A_17]: (r2_hidden(k2_mcart_1('#skF_10'), A_17) | ~r1_tarski('#skF_9', k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_14736])).
% 11.42/4.47  tff(c_14767, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_14751])).
% 11.42/4.47  tff(c_14981, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14972, c_14767])).
% 11.42/4.47  tff(c_14990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_14981])).
% 11.42/4.47  tff(c_14992, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_14751])).
% 11.42/4.47  tff(c_14627, plain, (![B_1644]: (~v1_xboole_0(B_1644) | ~r1_tarski('#skF_9', B_1644))), inference(resolution, [status(thm)], [c_14603, c_2])).
% 11.42/4.47  tff(c_15002, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14992, c_14627])).
% 11.42/4.47  tff(c_15020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14563, c_15002])).
% 11.42/4.47  tff(c_15021, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_10394])).
% 11.42/4.47  tff(c_15026, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_15021, c_48])).
% 11.42/4.47  tff(c_15163, plain, (![A_1719, C_1720, B_1721]: (r2_hidden(k2_mcart_1(A_1719), C_1720) | ~r2_hidden(A_1719, k2_zfmisc_1(B_1721, C_1720)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_15395, plain, (![A_1750, C_1751, A_1752, B_1753]: (r2_hidden(k2_mcart_1(A_1750), C_1751) | ~r2_hidden(A_1750, k3_zfmisc_1(A_1752, B_1753, C_1751)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_15163])).
% 11.42/4.47  tff(c_15418, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_15026, c_15395])).
% 11.42/4.47  tff(c_15429, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_15418, c_2])).
% 11.42/4.47  tff(c_15023, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15021, c_10381])).
% 11.42/4.47  tff(c_15430, plain, (![A_1754, B_1755, C_1756, D_1757]: (k7_mcart_1(A_1754, B_1755, C_1756, D_1757)=k2_mcart_1(D_1757) | ~m1_subset_1(D_1757, k3_zfmisc_1(A_1754, B_1755, C_1756)) | k1_xboole_0=C_1756 | k1_xboole_0=B_1755 | k1_xboole_0=A_1754)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_15434, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_14199, c_15430])).
% 11.42/4.47  tff(c_15478, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_15434])).
% 11.42/4.47  tff(c_15084, plain, (![C_1706, B_1707, A_1708]: (r2_hidden(C_1706, B_1707) | ~r2_hidden(C_1706, A_1708) | ~r1_tarski(A_1708, B_1707))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.47  tff(c_15182, plain, (![A_1722, B_1723]: (r2_hidden('#skF_1'(A_1722), B_1723) | ~r1_tarski(A_1722, B_1723) | v1_xboole_0(A_1722))), inference(resolution, [status(thm)], [c_4, c_15084])).
% 11.42/4.47  tff(c_15213, plain, (![B_1727, A_1728]: (~v1_xboole_0(B_1727) | ~r1_tarski(A_1728, B_1727) | v1_xboole_0(A_1728))), inference(resolution, [status(thm)], [c_15182, c_2])).
% 11.42/4.47  tff(c_15229, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_15213])).
% 11.42/4.47  tff(c_15230, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_15229])).
% 11.42/4.47  tff(c_15314, plain, (![A_1740, B_1741, C_1742]: (~r1_xboole_0(A_1740, B_1741) | ~r1_tarski(C_1742, B_1741) | ~r1_tarski(C_1742, A_1740))), inference(negUnitSimplification, [status(thm)], [c_15230, c_26])).
% 11.42/4.47  tff(c_15340, plain, (![C_1745, B_1746, A_1747]: (~r1_tarski(C_1745, B_1746) | ~r1_tarski(C_1745, k4_xboole_0(A_1747, B_1746)))), inference(resolution, [status(thm)], [c_28, c_15314])).
% 11.42/4.47  tff(c_15348, plain, (![B_1746]: (~r1_tarski(k1_xboole_0, B_1746))), inference(resolution, [status(thm)], [c_24, c_15340])).
% 11.42/4.47  tff(c_15353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_15348])).
% 11.42/4.47  tff(c_15354, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_15229])).
% 11.42/4.47  tff(c_15480, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_15478, c_15354])).
% 11.42/4.47  tff(c_15485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15023, c_15480])).
% 11.42/4.47  tff(c_15486, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_9' | k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_15434])).
% 11.42/4.47  tff(c_15535, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_15486])).
% 11.42/4.47  tff(c_15536, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15535, c_14196])).
% 11.42/4.47  tff(c_15539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15418, c_15536])).
% 11.42/4.47  tff(c_15540, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_15486])).
% 11.42/4.47  tff(c_15542, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_15540])).
% 11.42/4.47  tff(c_15546, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15542, c_15354])).
% 11.42/4.47  tff(c_15551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14226, c_15546])).
% 11.42/4.47  tff(c_15552, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_15540])).
% 11.42/4.47  tff(c_15558, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15552, c_15354])).
% 11.42/4.47  tff(c_15563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15429, c_15558])).
% 11.42/4.47  tff(c_15564, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_10395])).
% 11.42/4.47  tff(c_15571, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_15564, c_14199])).
% 11.42/4.47  tff(c_15949, plain, (![A_1836, B_1837, C_1838, D_1839]: (k7_mcart_1(A_1836, B_1837, C_1838, D_1839)=k2_mcart_1(D_1839) | ~m1_subset_1(D_1839, k3_zfmisc_1(A_1836, B_1837, C_1838)) | k1_xboole_0=C_1838 | k1_xboole_0=B_1837 | k1_xboole_0=A_1836)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_15953, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_15571, c_15949])).
% 11.42/4.47  tff(c_16300, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_15953])).
% 11.42/4.47  tff(c_16310, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16300, c_15916])).
% 11.42/4.47  tff(c_16315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15589, c_16310])).
% 11.42/4.47  tff(c_16317, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_15953])).
% 11.42/4.47  tff(c_16038, plain, (![A_1852, B_1853, C_1854, D_1855]: (k6_mcart_1(A_1852, B_1853, C_1854, D_1855)=k2_mcart_1(k1_mcart_1(D_1855)) | ~m1_subset_1(D_1855, k3_zfmisc_1(A_1852, B_1853, C_1854)) | k1_xboole_0=C_1854 | k1_xboole_0=B_1853 | k1_xboole_0=A_1852)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_16042, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_15571, c_16038])).
% 11.42/4.47  tff(c_16440, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_16317, c_16042])).
% 11.42/4.47  tff(c_16441, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_16440])).
% 11.42/4.47  tff(c_16457, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16441, c_15916])).
% 11.42/4.47  tff(c_15700, plain, (![A_1799, B_1800, C_1801]: (r2_hidden(k1_mcart_1(A_1799), B_1800) | ~r2_hidden(A_1799, k2_zfmisc_1(B_1800, C_1801)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_16136, plain, (![B_1873, C_1874]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1873, C_1874))), B_1873) | v1_xboole_0(k2_zfmisc_1(B_1873, C_1874)))), inference(resolution, [status(thm)], [c_4, c_15700])).
% 11.42/4.47  tff(c_16167, plain, (![B_1875, C_1876]: (~v1_xboole_0(B_1875) | v1_xboole_0(k2_zfmisc_1(B_1875, C_1876)))), inference(resolution, [status(thm)], [c_16136, c_2])).
% 11.42/4.47  tff(c_14212, plain, (![A_1582, B_1583]: (~v1_xboole_0(A_1582) | r1_tarski(A_1582, B_1583))), inference(resolution, [status(thm)], [c_14185, c_2])).
% 11.42/4.47  tff(c_14219, plain, (![A_1582]: (k1_xboole_0=A_1582 | ~v1_xboole_0(A_1582))), inference(resolution, [status(thm)], [c_14212, c_10401])).
% 11.42/4.47  tff(c_16178, plain, (![B_1877, C_1878]: (k2_zfmisc_1(B_1877, C_1878)=k1_xboole_0 | ~v1_xboole_0(B_1877))), inference(resolution, [status(thm)], [c_16167, c_14219])).
% 11.42/4.47  tff(c_16185, plain, (![C_1878]: (k2_zfmisc_1(k1_xboole_0, C_1878)=k1_xboole_0)), inference(resolution, [status(thm)], [c_15916, c_16178])).
% 11.42/4.47  tff(c_16451, plain, (![C_1878]: (k2_zfmisc_1('#skF_8', C_1878)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16441, c_16441, c_16185])).
% 11.42/4.47  tff(c_16615, plain, (![B_1907, C_1908]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1907, C_1908))), C_1908) | v1_xboole_0(k2_zfmisc_1(B_1907, C_1908)))), inference(resolution, [status(thm)], [c_4, c_15650])).
% 11.42/4.47  tff(c_16186, plain, (![C_1879]: (k2_zfmisc_1(k1_xboole_0, C_1879)=k1_xboole_0)), inference(resolution, [status(thm)], [c_15916, c_16178])).
% 11.42/4.47  tff(c_16270, plain, (![A_1888, C_1889]: (r2_hidden(k2_mcart_1(A_1888), C_1889) | ~r2_hidden(A_1888, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16186, c_36])).
% 11.42/4.47  tff(c_16298, plain, (![C_1889, A_1888]: (~v1_xboole_0(C_1889) | ~r2_hidden(A_1888, k1_xboole_0))), inference(resolution, [status(thm)], [c_16270, c_2])).
% 11.42/4.47  tff(c_16299, plain, (![A_1888]: (~r2_hidden(A_1888, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_16298])).
% 11.42/4.47  tff(c_16447, plain, (![A_1888]: (~r2_hidden(A_1888, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_16441, c_16299])).
% 11.42/4.47  tff(c_16685, plain, (![B_1910]: (v1_xboole_0(k2_zfmisc_1(B_1910, '#skF_8')))), inference(resolution, [status(thm)], [c_16615, c_16447])).
% 11.42/4.47  tff(c_16458, plain, (![A_1582]: (A_1582='#skF_8' | ~v1_xboole_0(A_1582))), inference(demodulation, [status(thm), theory('equality')], [c_16441, c_14219])).
% 11.42/4.47  tff(c_16703, plain, (![B_1911]: (k2_zfmisc_1(B_1911, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_16685, c_16458])).
% 11.42/4.47  tff(c_16728, plain, (![B_1911, C_27]: (k3_zfmisc_1(B_1911, '#skF_8', C_27)=k2_zfmisc_1('#skF_8', C_27))), inference(superposition, [status(thm), theory('equality')], [c_16703, c_34])).
% 11.42/4.47  tff(c_16750, plain, (![B_1911, C_27]: (k3_zfmisc_1(B_1911, '#skF_8', C_27)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16451, c_16728])).
% 11.42/4.47  tff(c_16878, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16750, c_70])).
% 11.42/4.47  tff(c_16884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16457, c_16878])).
% 11.42/4.47  tff(c_16886, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_16440])).
% 11.42/4.47  tff(c_16097, plain, (![A_1861, B_1862, C_1863, D_1864]: (k5_mcart_1(A_1861, B_1862, C_1863, D_1864)=k1_mcart_1(k1_mcart_1(D_1864)) | ~m1_subset_1(D_1864, k3_zfmisc_1(A_1861, B_1862, C_1863)) | k1_xboole_0=C_1863 | k1_xboole_0=B_1862 | k1_xboole_0=A_1861)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_16101, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_15571, c_16097])).
% 11.42/4.47  tff(c_16944, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_16317, c_16886, c_16101])).
% 11.42/4.47  tff(c_16945, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_16944])).
% 11.42/4.47  tff(c_15961, plain, (![B_1840]: (r2_hidden(k2_mcart_1('#skF_10'), B_1840) | ~r1_tarski('#skF_9', B_1840))), inference(resolution, [status(thm)], [c_15947, c_6])).
% 11.42/4.47  tff(c_16049, plain, (![B_1858, B_1859]: (r2_hidden(k2_mcart_1('#skF_10'), B_1858) | ~r1_tarski(B_1859, B_1858) | ~r1_tarski('#skF_9', B_1859))), inference(resolution, [status(thm)], [c_15961, c_6])).
% 11.42/4.47  tff(c_16061, plain, (![A_17]: (r2_hidden(k2_mcart_1('#skF_10'), A_17) | ~r1_tarski('#skF_9', k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_16049])).
% 11.42/4.47  tff(c_16067, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_16061])).
% 11.42/4.47  tff(c_16961, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_16945, c_16067])).
% 11.42/4.47  tff(c_16970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_16961])).
% 11.42/4.47  tff(c_16972, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_16944])).
% 11.42/4.47  tff(c_16316, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9' | k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_15953])).
% 11.42/4.47  tff(c_17274, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_16972, c_16886, c_16316])).
% 11.42/4.47  tff(c_15630, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15564, c_14196])).
% 11.42/4.47  tff(c_17275, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_17274, c_15630])).
% 11.42/4.47  tff(c_17278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15947, c_17275])).
% 11.42/4.47  tff(c_17279, plain, (![C_1889]: (~v1_xboole_0(C_1889))), inference(splitRight, [status(thm)], [c_16298])).
% 11.42/4.47  tff(c_17290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17279, c_15916])).
% 11.42/4.47  tff(c_17292, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_16061])).
% 11.42/4.47  tff(c_15985, plain, (![B_1840]: (~v1_xboole_0(B_1840) | ~r1_tarski('#skF_9', B_1840))), inference(resolution, [status(thm)], [c_15961, c_2])).
% 11.42/4.47  tff(c_17297, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_17292, c_15985])).
% 11.42/4.47  tff(c_17315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15916, c_17297])).
% 11.42/4.47  tff(c_17316, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_10394])).
% 11.42/4.47  tff(c_17321, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_17316, c_48])).
% 11.42/4.47  tff(c_17425, plain, (![A_1967, C_1968, B_1969]: (r2_hidden(k2_mcart_1(A_1967), C_1968) | ~r2_hidden(A_1967, k2_zfmisc_1(B_1969, C_1968)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_17664, plain, (![A_2003, C_2004, A_2005, B_2006]: (r2_hidden(k2_mcart_1(A_2003), C_2004) | ~r2_hidden(A_2003, k3_zfmisc_1(A_2005, B_2006, C_2004)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_17425])).
% 11.42/4.47  tff(c_17683, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_17321, c_17664])).
% 11.42/4.47  tff(c_17318, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17316, c_10381])).
% 11.42/4.47  tff(c_17839, plain, (![A_2028, B_2029, C_2030, D_2031]: (k7_mcart_1(A_2028, B_2029, C_2030, D_2031)=k2_mcart_1(D_2031) | ~m1_subset_1(D_2031, k3_zfmisc_1(A_2028, B_2029, C_2030)) | k1_xboole_0=C_2030 | k1_xboole_0=B_2029 | k1_xboole_0=A_2028)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_17843, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_15571, c_17839])).
% 11.42/4.47  tff(c_17883, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_17843])).
% 11.42/4.47  tff(c_17886, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17883, c_17655])).
% 11.42/4.47  tff(c_17891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17318, c_17886])).
% 11.42/4.47  tff(c_17892, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9' | k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_17843])).
% 11.42/4.47  tff(c_17982, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_17892])).
% 11.42/4.47  tff(c_17369, plain, (~r2_hidden(k7_mcart_1('#skF_4', '#skF_8', '#skF_9', '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15564, c_14196])).
% 11.42/4.47  tff(c_17983, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_17982, c_17369])).
% 11.42/4.47  tff(c_17986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17683, c_17983])).
% 11.42/4.47  tff(c_17987, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_17892])).
% 11.42/4.47  tff(c_17989, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_17987])).
% 11.42/4.47  tff(c_17997, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17989, c_17655])).
% 11.42/4.47  tff(c_17456, plain, (![A_1971, B_1972, C_1973]: (r2_hidden(k1_mcart_1(A_1971), B_1972) | ~r2_hidden(A_1971, k2_zfmisc_1(B_1972, C_1973)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_18178, plain, (![B_2071, C_2072]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2071, C_2072))), B_2071) | v1_xboole_0(k2_zfmisc_1(B_2071, C_2072)))), inference(resolution, [status(thm)], [c_4, c_17456])).
% 11.42/4.47  tff(c_18213, plain, (![B_2073, C_2074]: (~v1_xboole_0(B_2073) | v1_xboole_0(k2_zfmisc_1(B_2073, C_2074)))), inference(resolution, [status(thm)], [c_18178, c_2])).
% 11.42/4.47  tff(c_17998, plain, (![A_1582]: (A_1582='#skF_8' | ~v1_xboole_0(A_1582))), inference(demodulation, [status(thm), theory('equality')], [c_17989, c_14219])).
% 11.42/4.47  tff(c_18224, plain, (![B_2075, C_2076]: (k2_zfmisc_1(B_2075, C_2076)='#skF_8' | ~v1_xboole_0(B_2075))), inference(resolution, [status(thm)], [c_18213, c_17998])).
% 11.42/4.47  tff(c_18232, plain, (![C_2077]: (k2_zfmisc_1('#skF_8', C_2077)='#skF_8')), inference(resolution, [status(thm)], [c_17997, c_18224])).
% 11.42/4.47  tff(c_18289, plain, (![A_2083]: (r2_hidden(k1_mcart_1(A_2083), '#skF_8') | ~r2_hidden(A_2083, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18232, c_38])).
% 11.42/4.47  tff(c_18296, plain, (![A_2083]: (~v1_xboole_0('#skF_8') | ~r2_hidden(A_2083, '#skF_8'))), inference(resolution, [status(thm)], [c_18289, c_2])).
% 11.42/4.47  tff(c_18303, plain, (![A_2083]: (~r2_hidden(A_2083, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17997, c_18296])).
% 11.42/4.47  tff(c_18231, plain, (![C_2076]: (k2_zfmisc_1('#skF_8', C_2076)='#skF_8')), inference(resolution, [status(thm)], [c_17997, c_18224])).
% 11.42/4.47  tff(c_18443, plain, (![B_2095, C_2096]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2095, C_2096))), C_2096) | v1_xboole_0(k2_zfmisc_1(B_2095, C_2096)))), inference(resolution, [status(thm)], [c_4, c_17425])).
% 11.42/4.47  tff(c_18481, plain, (![B_2097]: (v1_xboole_0(k2_zfmisc_1(B_2097, '#skF_8')))), inference(resolution, [status(thm)], [c_18443, c_18303])).
% 11.42/4.47  tff(c_18505, plain, (![B_2098]: (k2_zfmisc_1(B_2098, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_18481, c_17998])).
% 11.42/4.47  tff(c_18530, plain, (![B_2098, C_27]: (k3_zfmisc_1(B_2098, '#skF_8', C_27)=k2_zfmisc_1('#skF_8', C_27))), inference(superposition, [status(thm), theory('equality')], [c_18505, c_34])).
% 11.42/4.47  tff(c_18552, plain, (![B_2098, C_27]: (k3_zfmisc_1(B_2098, '#skF_8', C_27)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18231, c_18530])).
% 11.42/4.47  tff(c_18604, plain, (r2_hidden('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18552, c_17321])).
% 11.42/4.47  tff(c_18609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18303, c_18604])).
% 11.42/4.47  tff(c_18610, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_17987])).
% 11.42/4.47  tff(c_17695, plain, (![B_2007]: (r2_hidden(k2_mcart_1('#skF_10'), B_2007) | ~r1_tarski('#skF_9', B_2007))), inference(resolution, [status(thm)], [c_17683, c_6])).
% 11.42/4.47  tff(c_17824, plain, (![B_2026, B_2027]: (r2_hidden(k2_mcart_1('#skF_10'), B_2026) | ~r1_tarski(B_2027, B_2026) | ~r1_tarski('#skF_9', B_2027))), inference(resolution, [status(thm)], [c_17695, c_6])).
% 11.42/4.47  tff(c_17833, plain, (![A_17]: (r2_hidden(k2_mcart_1('#skF_10'), A_17) | ~r1_tarski('#skF_9', k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_17824])).
% 11.42/4.47  tff(c_17834, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_17833])).
% 11.42/4.47  tff(c_18618, plain, (~r1_tarski('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_18610, c_17834])).
% 11.42/4.47  tff(c_18625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_18618])).
% 11.42/4.47  tff(c_18627, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_17833])).
% 11.42/4.47  tff(c_17719, plain, (![B_2007]: (~v1_xboole_0(B_2007) | ~r1_tarski('#skF_9', B_2007))), inference(resolution, [status(thm)], [c_17695, c_2])).
% 11.42/4.47  tff(c_18637, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18627, c_17719])).
% 11.42/4.47  tff(c_18655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17655, c_18637])).
% 11.42/4.47  tff(c_18656, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_10376])).
% 11.42/4.47  tff(c_18668, plain, (![A_2111, B_2112]: (r2_hidden('#skF_2'(A_2111, B_2112), A_2111) | r1_tarski(A_2111, B_2112))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.47  tff(c_18678, plain, (![A_2111, B_2112]: (~v1_xboole_0(A_2111) | r1_tarski(A_2111, B_2112))), inference(resolution, [status(thm)], [c_18668, c_2])).
% 11.42/4.47  tff(c_18680, plain, (![B_2115, A_2116]: (B_2115=A_2116 | ~r1_tarski(B_2115, A_2116) | ~r1_tarski(A_2116, B_2115))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.42/4.47  tff(c_18695, plain, ('#skF_5'='#skF_8' | ~r1_tarski('#skF_5', '#skF_8')), inference(resolution, [status(thm)], [c_87, c_18680])).
% 11.42/4.47  tff(c_18721, plain, (~r1_tarski('#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_18695])).
% 11.42/4.47  tff(c_20319, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_18678, c_18721])).
% 11.42/4.47  tff(c_18777, plain, (![C_2124, B_2125, A_2126]: (r2_hidden(C_2124, B_2125) | ~r2_hidden(C_2124, A_2126) | ~r1_tarski(A_2126, B_2125))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.47  tff(c_18891, plain, (![A_2145, B_2146]: (r2_hidden('#skF_1'(A_2145), B_2146) | ~r1_tarski(A_2145, B_2146) | v1_xboole_0(A_2145))), inference(resolution, [status(thm)], [c_4, c_18777])).
% 11.42/4.47  tff(c_18912, plain, (![B_2147, A_2148]: (~v1_xboole_0(B_2147) | ~r1_tarski(A_2148, B_2147) | v1_xboole_0(A_2148))), inference(resolution, [status(thm)], [c_18891, c_2])).
% 11.42/4.47  tff(c_18938, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_18912])).
% 11.42/4.47  tff(c_18960, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_18938])).
% 11.42/4.47  tff(c_18984, plain, (![A_2154, B_2155, C_2156]: (~r1_xboole_0(A_2154, B_2155) | ~r1_tarski(C_2156, B_2155) | ~r1_tarski(C_2156, A_2154))), inference(negUnitSimplification, [status(thm)], [c_18960, c_26])).
% 11.42/4.47  tff(c_19070, plain, (![C_2166, B_2167, A_2168]: (~r1_tarski(C_2166, B_2167) | ~r1_tarski(C_2166, k4_xboole_0(A_2168, B_2167)))), inference(resolution, [status(thm)], [c_28, c_18984])).
% 11.42/4.47  tff(c_19078, plain, (![B_2167]: (~r1_tarski(k1_xboole_0, B_2167))), inference(resolution, [status(thm)], [c_24, c_19070])).
% 11.42/4.47  tff(c_19083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_19078])).
% 11.42/4.47  tff(c_19084, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_18938])).
% 11.42/4.47  tff(c_18726, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_18678, c_18721])).
% 11.42/4.47  tff(c_18694, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_88, c_18680])).
% 11.42/4.47  tff(c_18722, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_18694])).
% 11.42/4.47  tff(c_18730, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_18678, c_18722])).
% 11.42/4.47  tff(c_19108, plain, (![A_2170, B_2171, C_2172, D_2173]: (k7_mcart_1(A_2170, B_2171, C_2172, D_2173)=k2_mcart_1(D_2173) | ~m1_subset_1(D_2173, k3_zfmisc_1(A_2170, B_2171, C_2172)) | k1_xboole_0=C_2172 | k1_xboole_0=B_2171 | k1_xboole_0=A_2170)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_19112, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_19108])).
% 11.42/4.47  tff(c_19158, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_19112])).
% 11.42/4.47  tff(c_19160, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19158, c_19084])).
% 11.42/4.47  tff(c_19165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18730, c_19160])).
% 11.42/4.47  tff(c_19167, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_19112])).
% 11.42/4.47  tff(c_19285, plain, (![A_2197, B_2198, C_2199, D_2200]: (k6_mcart_1(A_2197, B_2198, C_2199, D_2200)=k2_mcart_1(k1_mcart_1(D_2200)) | ~m1_subset_1(D_2200, k3_zfmisc_1(A_2197, B_2198, C_2199)) | k1_xboole_0=C_2199 | k1_xboole_0=B_2198 | k1_xboole_0=A_2197)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_19288, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_19285])).
% 11.42/4.47  tff(c_19291, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_19167, c_19288])).
% 11.42/4.47  tff(c_19414, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_19291])).
% 11.42/4.47  tff(c_19420, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_19414, c_19084])).
% 11.42/4.47  tff(c_19425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18726, c_19420])).
% 11.42/4.47  tff(c_19426, plain, (k1_xboole_0='#skF_6' | k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_19291])).
% 11.42/4.47  tff(c_19458, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(splitLeft, [status(thm)], [c_19426])).
% 11.42/4.47  tff(c_18850, plain, (![A_2138, B_2139, C_2140]: (r2_hidden(k1_mcart_1(A_2138), B_2139) | ~r2_hidden(A_2138, k2_zfmisc_1(B_2139, C_2140)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_20180, plain, (![A_2276, A_2277, B_2278, C_2279]: (r2_hidden(k1_mcart_1(A_2276), k2_zfmisc_1(A_2277, B_2278)) | ~r2_hidden(A_2276, k3_zfmisc_1(A_2277, B_2278, C_2279)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_18850])).
% 11.42/4.47  tff(c_20244, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_48, c_20180])).
% 11.42/4.47  tff(c_20249, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_20244, c_36])).
% 11.42/4.47  tff(c_20258, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_19458, c_20249])).
% 11.42/4.47  tff(c_20260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18656, c_20258])).
% 11.42/4.47  tff(c_20261, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_19426])).
% 11.42/4.47  tff(c_18831, plain, (![A_2135, C_2136, B_2137]: (r2_hidden(k2_mcart_1(A_2135), C_2136) | ~r2_hidden(A_2135, k2_zfmisc_1(B_2137, C_2136)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_19183, plain, (![A_2181, C_2182, A_2183, B_2184]: (r2_hidden(k2_mcart_1(A_2181), C_2182) | ~r2_hidden(A_2181, k3_zfmisc_1(A_2183, B_2184, C_2182)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_18831])).
% 11.42/4.47  tff(c_19213, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_48, c_19183])).
% 11.42/4.47  tff(c_19229, plain, (![B_2189]: (r2_hidden(k2_mcart_1('#skF_10'), B_2189) | ~r1_tarski('#skF_9', B_2189))), inference(resolution, [status(thm)], [c_19213, c_6])).
% 11.42/4.47  tff(c_19299, plain, (![B_2203, B_2204]: (r2_hidden(k2_mcart_1('#skF_10'), B_2203) | ~r1_tarski(B_2204, B_2203) | ~r1_tarski('#skF_9', B_2204))), inference(resolution, [status(thm)], [c_19229, c_6])).
% 11.42/4.47  tff(c_19319, plain, (![A_17]: (r2_hidden(k2_mcart_1('#skF_10'), A_17) | ~r1_tarski('#skF_9', k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_19299])).
% 11.42/4.47  tff(c_19340, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_19319])).
% 11.42/4.47  tff(c_20264, plain, (~r1_tarski('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20261, c_19340])).
% 11.42/4.47  tff(c_20275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_20264])).
% 11.42/4.47  tff(c_20277, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_19319])).
% 11.42/4.47  tff(c_18657, plain, (r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_10376])).
% 11.42/4.47  tff(c_19137, plain, (![B_2179]: (r2_hidden(k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), B_2179) | ~r1_tarski('#skF_9', B_2179))), inference(resolution, [status(thm)], [c_18657, c_18777])).
% 11.42/4.47  tff(c_19157, plain, (![B_2179]: (~v1_xboole_0(B_2179) | ~r1_tarski('#skF_9', B_2179))), inference(resolution, [status(thm)], [c_19137, c_2])).
% 11.42/4.47  tff(c_20282, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_20277, c_19157])).
% 11.42/4.47  tff(c_20300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19084, c_20282])).
% 11.42/4.47  tff(c_20301, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_18694])).
% 11.42/4.47  tff(c_20304, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20301, c_10381])).
% 11.42/4.47  tff(c_20891, plain, (![A_2361, B_2362, C_2363, D_2364]: (k7_mcart_1(A_2361, B_2362, C_2363, D_2364)=k2_mcart_1(D_2364) | ~m1_subset_1(D_2364, k3_zfmisc_1(A_2361, B_2362, C_2363)) | k1_xboole_0=C_2363 | k1_xboole_0=B_2362 | k1_xboole_0=A_2361)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_20895, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_20891])).
% 11.42/4.47  tff(c_20912, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_20895])).
% 11.42/4.47  tff(c_20914, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20912, c_20661])).
% 11.42/4.47  tff(c_20919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20304, c_20914])).
% 11.42/4.47  tff(c_20921, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_20895])).
% 11.42/4.47  tff(c_21018, plain, (![A_2380, B_2381, C_2382, D_2383]: (k5_mcart_1(A_2380, B_2381, C_2382, D_2383)=k1_mcart_1(k1_mcart_1(D_2383)) | ~m1_subset_1(D_2383, k3_zfmisc_1(A_2380, B_2381, C_2382)) | k1_xboole_0=C_2382 | k1_xboole_0=B_2381 | k1_xboole_0=A_2380)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_21021, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_21018])).
% 11.42/4.47  tff(c_21024, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_20921, c_21021])).
% 11.42/4.47  tff(c_21044, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_21024])).
% 11.42/4.47  tff(c_21050, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21044, c_20661])).
% 11.42/4.47  tff(c_21055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20319, c_21050])).
% 11.42/4.47  tff(c_21057, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_21024])).
% 11.42/4.47  tff(c_20931, plain, (![A_2366, B_2367, C_2368, D_2369]: (k6_mcart_1(A_2366, B_2367, C_2368, D_2369)=k2_mcart_1(k1_mcart_1(D_2369)) | ~m1_subset_1(D_2369, k3_zfmisc_1(A_2366, B_2367, C_2368)) | k1_xboole_0=C_2368 | k1_xboole_0=B_2367 | k1_xboole_0=A_2366)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_20934, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_50, c_20931])).
% 11.42/4.47  tff(c_20937, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_20921, c_20934])).
% 11.42/4.47  tff(c_21328, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_21057, c_20937])).
% 11.42/4.47  tff(c_21329, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_21328])).
% 11.42/4.47  tff(c_20308, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_20301, c_48])).
% 11.42/4.47  tff(c_20459, plain, (![A_2300, C_2301, B_2302]: (r2_hidden(k2_mcart_1(A_2300), C_2301) | ~r2_hidden(A_2300, k2_zfmisc_1(B_2302, C_2301)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_20670, plain, (![A_2331, C_2332, A_2333, B_2334]: (r2_hidden(k2_mcart_1(A_2331), C_2332) | ~r2_hidden(A_2331, k3_zfmisc_1(A_2333, B_2334, C_2332)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_20459])).
% 11.42/4.47  tff(c_20689, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_20308, c_20670])).
% 11.42/4.47  tff(c_20701, plain, (![B_2335]: (r2_hidden(k2_mcart_1('#skF_10'), B_2335) | ~r1_tarski('#skF_9', B_2335))), inference(resolution, [status(thm)], [c_20689, c_6])).
% 11.42/4.47  tff(c_20873, plain, (![B_2359, B_2360]: (r2_hidden(k2_mcart_1('#skF_10'), B_2359) | ~r1_tarski(B_2360, B_2359) | ~r1_tarski('#skF_9', B_2360))), inference(resolution, [status(thm)], [c_20701, c_6])).
% 11.42/4.47  tff(c_20890, plain, (![A_17]: (r2_hidden(k2_mcart_1('#skF_10'), A_17) | ~r1_tarski('#skF_9', k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_20873])).
% 11.42/4.47  tff(c_20911, plain, (~r1_tarski('#skF_9', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_20890])).
% 11.42/4.47  tff(c_21340, plain, (~r1_tarski('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21329, c_20911])).
% 11.42/4.47  tff(c_21349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_21340])).
% 11.42/4.47  tff(c_21350, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_21328])).
% 11.42/4.47  tff(c_20430, plain, (![A_2296, B_2297, C_2298]: (k2_zfmisc_1(k2_zfmisc_1(A_2296, B_2297), C_2298)=k3_zfmisc_1(A_2296, B_2297, C_2298))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.42/4.47  tff(c_22375, plain, (![A_2492, A_2493, B_2494, C_2495]: (r2_hidden(k1_mcart_1(A_2492), k2_zfmisc_1(A_2493, B_2494)) | ~r2_hidden(A_2492, k3_zfmisc_1(A_2493, B_2494, C_2495)))), inference(superposition, [status(thm), theory('equality')], [c_20430, c_38])).
% 11.42/4.47  tff(c_22439, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_20308, c_22375])).
% 11.42/4.47  tff(c_22445, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_22439, c_36])).
% 11.42/4.47  tff(c_22454, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_21350, c_22445])).
% 11.42/4.47  tff(c_22456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18656, c_22454])).
% 11.42/4.47  tff(c_22458, plain, (r1_tarski('#skF_9', k1_xboole_0)), inference(splitRight, [status(thm)], [c_20890])).
% 11.42/4.47  tff(c_20725, plain, (![B_2335]: (~v1_xboole_0(B_2335) | ~r1_tarski('#skF_9', B_2335))), inference(resolution, [status(thm)], [c_20701, c_2])).
% 11.42/4.47  tff(c_22463, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_22458, c_20725])).
% 11.42/4.47  tff(c_22481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20661, c_22463])).
% 11.42/4.47  tff(c_22482, plain, ('#skF_5'='#skF_8'), inference(splitRight, [status(thm)], [c_18695])).
% 11.42/4.47  tff(c_22485, plain, (~r2_hidden(k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22482, c_18656])).
% 11.42/4.47  tff(c_22559, plain, (![C_2503, B_2504, A_2505]: (r2_hidden(C_2503, B_2504) | ~r2_hidden(C_2503, A_2505) | ~r1_tarski(A_2505, B_2504))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.47  tff(c_22660, plain, (![A_2519, B_2520]: (r2_hidden('#skF_1'(A_2519), B_2520) | ~r1_tarski(A_2519, B_2520) | v1_xboole_0(A_2519))), inference(resolution, [status(thm)], [c_4, c_22559])).
% 11.42/4.47  tff(c_22681, plain, (![B_2521, A_2522]: (~v1_xboole_0(B_2521) | ~r1_tarski(A_2522, B_2521) | v1_xboole_0(A_2522))), inference(resolution, [status(thm)], [c_22660, c_2])).
% 11.42/4.47  tff(c_22703, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_22681])).
% 11.42/4.47  tff(c_22704, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_22703])).
% 11.42/4.47  tff(c_22727, plain, (![A_2525, B_2526, C_2527]: (~r1_xboole_0(A_2525, B_2526) | ~r1_tarski(C_2527, B_2526) | ~r1_tarski(C_2527, A_2525))), inference(negUnitSimplification, [status(thm)], [c_22704, c_26])).
% 11.42/4.47  tff(c_22814, plain, (![C_2539, B_2540, A_2541]: (~r1_tarski(C_2539, B_2540) | ~r1_tarski(C_2539, k4_xboole_0(A_2541, B_2540)))), inference(resolution, [status(thm)], [c_28, c_22727])).
% 11.42/4.47  tff(c_22822, plain, (![B_2540]: (~r1_tarski(k1_xboole_0, B_2540))), inference(resolution, [status(thm)], [c_24, c_22814])).
% 11.42/4.47  tff(c_22827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22822])).
% 11.42/4.47  tff(c_22828, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_22703])).
% 11.42/4.47  tff(c_22501, plain, (~r1_tarski('#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_18694])).
% 11.42/4.47  tff(c_22505, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_18678, c_22501])).
% 11.42/4.47  tff(c_22488, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_22482, c_50])).
% 11.42/4.47  tff(c_22959, plain, (![A_2561, B_2562, C_2563, D_2564]: (k7_mcart_1(A_2561, B_2562, C_2563, D_2564)=k2_mcart_1(D_2564) | ~m1_subset_1(D_2564, k3_zfmisc_1(A_2561, B_2562, C_2563)) | k1_xboole_0=C_2563 | k1_xboole_0=B_2562 | k1_xboole_0=A_2561)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_22963, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22488, c_22959])).
% 11.42/4.47  tff(c_23020, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_22963])).
% 11.42/4.47  tff(c_23022, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_23020, c_22828])).
% 11.42/4.47  tff(c_23027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22505, c_23022])).
% 11.42/4.47  tff(c_23029, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_22963])).
% 11.42/4.47  tff(c_23059, plain, (![A_2574, B_2575, C_2576, D_2577]: (k5_mcart_1(A_2574, B_2575, C_2576, D_2577)=k1_mcart_1(k1_mcart_1(D_2577)) | ~m1_subset_1(D_2577, k3_zfmisc_1(A_2574, B_2575, C_2576)) | k1_xboole_0=C_2576 | k1_xboole_0=B_2575 | k1_xboole_0=A_2574)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_23062, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22488, c_23059])).
% 11.42/4.47  tff(c_23065, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_23029, c_23062])).
% 11.42/4.47  tff(c_23889, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_23065])).
% 11.42/4.47  tff(c_22612, plain, (![A_2512, C_2513, B_2514]: (r2_hidden(k2_mcart_1(A_2512), C_2513) | ~r2_hidden(A_2512, k2_zfmisc_1(B_2514, C_2513)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_23294, plain, (![B_2608, C_2609]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2608, C_2609))), C_2609) | v1_xboole_0(k2_zfmisc_1(B_2608, C_2609)))), inference(resolution, [status(thm)], [c_4, c_22612])).
% 11.42/4.47  tff(c_23323, plain, (![C_2610, B_2611]: (~v1_xboole_0(C_2610) | v1_xboole_0(k2_zfmisc_1(B_2611, C_2610)))), inference(resolution, [status(thm)], [c_23294, c_2])).
% 11.42/4.47  tff(c_18702, plain, (![A_2117]: (k1_xboole_0=A_2117 | ~r1_tarski(A_2117, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_18680])).
% 11.42/4.47  tff(c_18715, plain, (![A_2111]: (k1_xboole_0=A_2111 | ~v1_xboole_0(A_2111))), inference(resolution, [status(thm)], [c_18678, c_18702])).
% 11.42/4.47  tff(c_23334, plain, (![B_2612, C_2613]: (k2_zfmisc_1(B_2612, C_2613)=k1_xboole_0 | ~v1_xboole_0(C_2613))), inference(resolution, [status(thm)], [c_23323, c_18715])).
% 11.42/4.47  tff(c_23341, plain, (![B_2614]: (k2_zfmisc_1(B_2614, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22828, c_23334])).
% 11.42/4.47  tff(c_23552, plain, (![A_2633]: (r2_hidden(k2_mcart_1(A_2633), k1_xboole_0) | ~r2_hidden(A_2633, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_23341, c_36])).
% 11.42/4.47  tff(c_23568, plain, (![A_2633]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_2633, k1_xboole_0))), inference(resolution, [status(thm)], [c_23552, c_2])).
% 11.42/4.47  tff(c_23578, plain, (![A_2633]: (~r2_hidden(A_2633, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22828, c_23568])).
% 11.42/4.47  tff(c_23897, plain, (![A_2633]: (~r2_hidden(A_2633, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_23889, c_23578])).
% 11.42/4.47  tff(c_22629, plain, (![A_2515, B_2516, C_2517]: (k2_zfmisc_1(k2_zfmisc_1(A_2515, B_2516), C_2517)=k3_zfmisc_1(A_2515, B_2516, C_2517))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.42/4.47  tff(c_23958, plain, (![A_2655, A_2656, B_2657, C_2658]: (r2_hidden(k1_mcart_1(A_2655), k2_zfmisc_1(A_2656, B_2657)) | ~r2_hidden(A_2655, k3_zfmisc_1(A_2656, B_2657, C_2658)))), inference(superposition, [status(thm), theory('equality')], [c_22629, c_38])).
% 11.42/4.47  tff(c_24012, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_48, c_23958])).
% 11.42/4.47  tff(c_24092, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_24012, c_36])).
% 11.42/4.47  tff(c_24103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23897, c_24092])).
% 11.42/4.47  tff(c_24105, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_23065])).
% 11.42/4.47  tff(c_23148, plain, (![A_2583, B_2584, C_2585, D_2586]: (k6_mcart_1(A_2583, B_2584, C_2585, D_2586)=k2_mcart_1(k1_mcart_1(D_2586)) | ~m1_subset_1(D_2586, k3_zfmisc_1(A_2583, B_2584, C_2585)) | k1_xboole_0=C_2585 | k1_xboole_0=B_2584 | k1_xboole_0=A_2583)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_23151, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22488, c_23148])).
% 11.42/4.47  tff(c_23154, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_23029, c_23151])).
% 11.42/4.47  tff(c_24280, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_24105, c_23154])).
% 11.42/4.47  tff(c_24281, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_24280])).
% 11.42/4.47  tff(c_22847, plain, (![A_2545, C_2546, A_2547, B_2548]: (r2_hidden(k2_mcart_1(A_2545), C_2546) | ~r2_hidden(A_2545, k3_zfmisc_1(A_2547, B_2548, C_2546)))), inference(superposition, [status(thm), theory('equality')], [c_22629, c_36])).
% 11.42/4.47  tff(c_22869, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_48, c_22847])).
% 11.42/4.47  tff(c_22878, plain, (![B_2549]: (r2_hidden(k2_mcart_1('#skF_10'), B_2549) | ~r1_tarski('#skF_9', B_2549))), inference(resolution, [status(thm)], [c_22869, c_6])).
% 11.42/4.47  tff(c_23066, plain, (![B_2578, B_2579]: (r2_hidden(k2_mcart_1('#skF_10'), B_2578) | ~r1_tarski(B_2579, B_2578) | ~r1_tarski('#skF_9', B_2579))), inference(resolution, [status(thm)], [c_22878, c_6])).
% 11.42/4.47  tff(c_23072, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_6') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_86, c_23066])).
% 11.42/4.47  tff(c_23081, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_23072])).
% 11.42/4.47  tff(c_23109, plain, (![B_2581]: (r2_hidden(k2_mcart_1('#skF_10'), B_2581) | ~r1_tarski('#skF_6', B_2581))), inference(resolution, [status(thm)], [c_23081, c_6])).
% 11.42/4.47  tff(c_23200, plain, (![B_2599, B_2600]: (r2_hidden(k2_mcart_1('#skF_10'), B_2599) | ~r1_tarski(B_2600, B_2599) | ~r1_tarski('#skF_6', B_2600))), inference(resolution, [status(thm)], [c_23109, c_6])).
% 11.42/4.47  tff(c_23216, plain, (![A_17]: (r2_hidden(k2_mcart_1('#skF_10'), A_17) | ~r1_tarski('#skF_6', k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_23200])).
% 11.42/4.47  tff(c_23247, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_23216])).
% 11.42/4.47  tff(c_24301, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24281, c_23247])).
% 11.42/4.47  tff(c_24313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_24301])).
% 11.42/4.47  tff(c_24314, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_24280])).
% 11.42/4.47  tff(c_24557, plain, (![A_2694, A_2695, B_2696, C_2697]: (r2_hidden(k1_mcart_1(A_2694), k2_zfmisc_1(A_2695, B_2696)) | ~r2_hidden(A_2694, k3_zfmisc_1(A_2695, B_2696, C_2697)))), inference(superposition, [status(thm), theory('equality')], [c_22629, c_38])).
% 11.42/4.47  tff(c_24624, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_48, c_24557])).
% 11.42/4.47  tff(c_24627, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_24624, c_36])).
% 11.42/4.47  tff(c_24636, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24314, c_24627])).
% 11.42/4.47  tff(c_24638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22485, c_24636])).
% 11.42/4.47  tff(c_24640, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_23216])).
% 11.42/4.47  tff(c_23136, plain, (![B_2581]: (~v1_xboole_0(B_2581) | ~r1_tarski('#skF_6', B_2581))), inference(resolution, [status(thm)], [c_23109, c_2])).
% 11.42/4.47  tff(c_24645, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_24640, c_23136])).
% 11.42/4.47  tff(c_24665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22828, c_24645])).
% 11.42/4.47  tff(c_24666, plain, ('#skF_7'='#skF_4'), inference(splitRight, [status(thm)], [c_18694])).
% 11.42/4.47  tff(c_24671, plain, (r2_hidden('#skF_10', k3_zfmisc_1('#skF_4', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_24666, c_48])).
% 11.42/4.47  tff(c_24738, plain, (![A_2705, B_2706, C_2707]: (k2_zfmisc_1(k2_zfmisc_1(A_2705, B_2706), C_2707)=k3_zfmisc_1(A_2705, B_2706, C_2707))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.42/4.47  tff(c_25021, plain, (![A_2747, C_2748, A_2749, B_2750]: (r2_hidden(k2_mcart_1(A_2747), C_2748) | ~r2_hidden(A_2747, k3_zfmisc_1(A_2749, B_2750, C_2748)))), inference(superposition, [status(thm), theory('equality')], [c_24738, c_36])).
% 11.42/4.47  tff(c_25040, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_24671, c_25021])).
% 11.42/4.47  tff(c_25052, plain, (![B_2751]: (r2_hidden(k2_mcart_1('#skF_10'), B_2751) | ~r1_tarski('#skF_9', B_2751))), inference(resolution, [status(thm)], [c_25040, c_6])).
% 11.42/4.47  tff(c_25236, plain, (![B_2780, B_2781]: (r2_hidden(k2_mcart_1('#skF_10'), B_2780) | ~r1_tarski(B_2781, B_2780) | ~r1_tarski('#skF_9', B_2781))), inference(resolution, [status(thm)], [c_25052, c_6])).
% 11.42/4.47  tff(c_25240, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_6') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_86, c_25236])).
% 11.42/4.47  tff(c_25248, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_25240])).
% 11.42/4.47  tff(c_24668, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24666, c_10381])).
% 11.42/4.47  tff(c_25133, plain, (![A_2763, B_2764, C_2765, D_2766]: (k7_mcart_1(A_2763, B_2764, C_2765, D_2766)=k2_mcart_1(D_2766) | ~m1_subset_1(D_2766, k3_zfmisc_1(A_2763, B_2764, C_2765)) | k1_xboole_0=C_2765 | k1_xboole_0=B_2764 | k1_xboole_0=A_2763)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_25137, plain, (k7_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22488, c_25133])).
% 11.42/4.47  tff(c_25180, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_25137])).
% 11.42/4.47  tff(c_24786, plain, (![C_2714, B_2715, A_2716]: (r2_hidden(C_2714, B_2715) | ~r2_hidden(C_2714, A_2716) | ~r1_tarski(A_2716, B_2715))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.42/4.47  tff(c_24839, plain, (![A_2721, B_2722]: (r2_hidden('#skF_1'(A_2721), B_2722) | ~r1_tarski(A_2721, B_2722) | v1_xboole_0(A_2721))), inference(resolution, [status(thm)], [c_4, c_24786])).
% 11.42/4.47  tff(c_24860, plain, (![B_2723, A_2724]: (~v1_xboole_0(B_2723) | ~r1_tarski(A_2724, B_2723) | v1_xboole_0(A_2724))), inference(resolution, [status(thm)], [c_24839, c_2])).
% 11.42/4.47  tff(c_24877, plain, (![A_17]: (~v1_xboole_0(A_17) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_24860])).
% 11.42/4.47  tff(c_24878, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_24877])).
% 11.42/4.47  tff(c_24901, plain, (![A_2727, B_2728, C_2729]: (~r1_xboole_0(A_2727, B_2728) | ~r1_tarski(C_2729, B_2728) | ~r1_tarski(C_2729, A_2727))), inference(negUnitSimplification, [status(thm)], [c_24878, c_26])).
% 11.42/4.47  tff(c_24988, plain, (![C_2741, B_2742, A_2743]: (~r1_tarski(C_2741, B_2742) | ~r1_tarski(C_2741, k4_xboole_0(A_2743, B_2742)))), inference(resolution, [status(thm)], [c_28, c_24901])).
% 11.42/4.47  tff(c_24996, plain, (![B_2742]: (~r1_tarski(k1_xboole_0, B_2742))), inference(resolution, [status(thm)], [c_24, c_24988])).
% 11.42/4.47  tff(c_25001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_24996])).
% 11.42/4.47  tff(c_25002, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_24877])).
% 11.42/4.47  tff(c_25182, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25180, c_25002])).
% 11.42/4.47  tff(c_25187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24668, c_25182])).
% 11.42/4.47  tff(c_25189, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_25137])).
% 11.42/4.47  tff(c_25229, plain, (![A_2776, B_2777, C_2778, D_2779]: (k5_mcart_1(A_2776, B_2777, C_2778, D_2779)=k1_mcart_1(k1_mcart_1(D_2779)) | ~m1_subset_1(D_2779, k3_zfmisc_1(A_2776, B_2777, C_2778)) | k1_xboole_0=C_2778 | k1_xboole_0=B_2777 | k1_xboole_0=A_2776)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_25232, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22488, c_25229])).
% 11.42/4.47  tff(c_25235, plain, (k1_mcart_1(k1_mcart_1('#skF_10'))=k5_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_25189, c_25232])).
% 11.42/4.47  tff(c_25552, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_25235])).
% 11.42/4.47  tff(c_25565, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_25552, c_25002])).
% 11.42/4.47  tff(c_24689, plain, (![A_2698, C_2699, B_2700]: (r2_hidden(k2_mcart_1(A_2698), C_2699) | ~r2_hidden(A_2698, k2_zfmisc_1(B_2700, C_2699)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_25684, plain, (![B_2824, C_2825]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2824, C_2825))), C_2825) | v1_xboole_0(k2_zfmisc_1(B_2824, C_2825)))), inference(resolution, [status(thm)], [c_4, c_24689])).
% 11.42/4.47  tff(c_25731, plain, (![C_2827, B_2828]: (~v1_xboole_0(C_2827) | v1_xboole_0(k2_zfmisc_1(B_2828, C_2827)))), inference(resolution, [status(thm)], [c_25684, c_2])).
% 11.42/4.47  tff(c_25566, plain, (![A_2111]: (A_2111='#skF_8' | ~v1_xboole_0(A_2111))), inference(demodulation, [status(thm), theory('equality')], [c_25552, c_18715])).
% 11.42/4.47  tff(c_25792, plain, (![B_2831, C_2832]: (k2_zfmisc_1(B_2831, C_2832)='#skF_8' | ~v1_xboole_0(C_2832))), inference(resolution, [status(thm)], [c_25731, c_25566])).
% 11.42/4.47  tff(c_25798, plain, (![B_2831]: (k2_zfmisc_1(B_2831, '#skF_8')='#skF_8')), inference(resolution, [status(thm)], [c_25565, c_25792])).
% 11.42/4.47  tff(c_24808, plain, (![A_2717, B_2718, C_2719]: (r2_hidden(k1_mcart_1(A_2717), B_2718) | ~r2_hidden(A_2717, k2_zfmisc_1(B_2718, C_2719)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.42/4.47  tff(c_25998, plain, (![A_2846, A_2847, B_2848, C_2849]: (r2_hidden(k1_mcart_1(A_2846), k2_zfmisc_1(A_2847, B_2848)) | ~r2_hidden(A_2846, k3_zfmisc_1(A_2847, B_2848, C_2849)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_24808])).
% 11.42/4.47  tff(c_26031, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_24671, c_25998])).
% 11.42/4.47  tff(c_26055, plain, (r2_hidden(k1_mcart_1('#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_25798, c_26031])).
% 11.42/4.47  tff(c_25385, plain, (![A_2803, B_2804, B_2805]: (r2_hidden('#skF_3'(A_2803, B_2804), B_2805) | ~r1_tarski(A_2803, B_2805) | r1_xboole_0(A_2803, B_2804))), inference(resolution, [status(thm)], [c_16, c_24786])).
% 11.42/4.47  tff(c_25414, plain, (![B_2806, A_2807, B_2808]: (~v1_xboole_0(B_2806) | ~r1_tarski(A_2807, B_2806) | r1_xboole_0(A_2807, B_2808))), inference(resolution, [status(thm)], [c_25385, c_2])).
% 11.42/4.47  tff(c_25426, plain, (![A_17, B_2808]: (~v1_xboole_0(A_17) | r1_xboole_0(k1_xboole_0, B_2808))), inference(resolution, [status(thm)], [c_24, c_25414])).
% 11.42/4.47  tff(c_25427, plain, (![A_17]: (~v1_xboole_0(A_17))), inference(splitLeft, [status(thm)], [c_25426])).
% 11.42/4.47  tff(c_25437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25427, c_25002])).
% 11.42/4.47  tff(c_25438, plain, (![B_2808]: (r1_xboole_0(k1_xboole_0, B_2808))), inference(splitRight, [status(thm)], [c_25426])).
% 11.42/4.47  tff(c_25576, plain, (![B_2817]: (r1_xboole_0('#skF_8', B_2817))), inference(demodulation, [status(thm), theory('equality')], [c_25552, c_25438])).
% 11.42/4.47  tff(c_25582, plain, (![C_14, B_2817]: (~r2_hidden(C_14, B_2817) | ~r2_hidden(C_14, '#skF_8'))), inference(resolution, [status(thm)], [c_25576, c_12])).
% 11.42/4.47  tff(c_26061, plain, (~r2_hidden(k1_mcart_1('#skF_10'), '#skF_8')), inference(resolution, [status(thm)], [c_26055, c_25582])).
% 11.42/4.47  tff(c_26070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26055, c_26061])).
% 11.42/4.47  tff(c_26072, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_25235])).
% 11.42/4.47  tff(c_25318, plain, (![A_2785, B_2786, C_2787, D_2788]: (k6_mcart_1(A_2785, B_2786, C_2787, D_2788)=k2_mcart_1(k1_mcart_1(D_2788)) | ~m1_subset_1(D_2788, k3_zfmisc_1(A_2785, B_2786, C_2787)) | k1_xboole_0=C_2787 | k1_xboole_0=B_2786 | k1_xboole_0=A_2785)), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.42/4.47  tff(c_25321, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22488, c_25318])).
% 11.42/4.47  tff(c_25324, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_25189, c_25321])).
% 11.42/4.47  tff(c_26077, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_26072, c_25324])).
% 11.42/4.47  tff(c_26078, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_26077])).
% 11.42/4.47  tff(c_25439, plain, (![B_2809]: (r1_xboole_0(k1_xboole_0, B_2809))), inference(splitRight, [status(thm)], [c_25426])).
% 11.42/4.47  tff(c_25446, plain, (![C_2810, B_2811]: (~r2_hidden(C_2810, B_2811) | ~r2_hidden(C_2810, k1_xboole_0))), inference(resolution, [status(thm)], [c_25439, c_12])).
% 11.42/4.47  tff(c_25478, plain, (~r2_hidden(k2_mcart_1('#skF_10'), k1_xboole_0)), inference(resolution, [status(thm)], [c_25040, c_25446])).
% 11.42/4.47  tff(c_26083, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_26078, c_25478])).
% 11.42/4.47  tff(c_26099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25248, c_26083])).
% 11.42/4.47  tff(c_26100, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10')), inference(splitRight, [status(thm)], [c_26077])).
% 11.42/4.47  tff(c_26848, plain, (![A_2912, A_2913, B_2914, C_2915]: (r2_hidden(k1_mcart_1(A_2912), k2_zfmisc_1(A_2913, B_2914)) | ~r2_hidden(A_2912, k3_zfmisc_1(A_2913, B_2914, C_2915)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_24808])).
% 11.42/4.47  tff(c_26912, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_24671, c_26848])).
% 11.42/4.47  tff(c_26922, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_26912, c_36])).
% 11.42/4.47  tff(c_26930, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_8', '#skF_6', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26100, c_26922])).
% 11.42/4.47  tff(c_26932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22485, c_26930])).
% 11.42/4.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.42/4.47  
% 11.42/4.47  Inference rules
% 11.42/4.47  ----------------------
% 11.42/4.48  #Ref     : 0
% 11.42/4.48  #Sup     : 6336
% 11.42/4.48  #Fact    : 0
% 11.42/4.48  #Define  : 0
% 11.42/4.48  #Split   : 154
% 11.42/4.48  #Chain   : 0
% 11.42/4.48  #Close   : 0
% 11.42/4.48  
% 11.42/4.48  Ordering : KBO
% 11.42/4.48  
% 11.42/4.48  Simplification rules
% 11.42/4.48  ----------------------
% 11.42/4.48  #Subsume      : 1865
% 11.42/4.48  #Demod        : 2496
% 11.42/4.48  #Tautology    : 1597
% 11.42/4.48  #SimpNegUnit  : 387
% 11.42/4.48  #BackRed      : 809
% 11.42/4.48  
% 11.42/4.48  #Partial instantiations: 0
% 11.42/4.48  #Strategies tried      : 1
% 11.42/4.48  
% 11.42/4.48  Timing (in seconds)
% 11.42/4.48  ----------------------
% 11.89/4.48  Preprocessing        : 0.41
% 11.89/4.48  Parsing              : 0.19
% 11.89/4.48  CNF conversion       : 0.04
% 11.89/4.48  Main loop            : 2.89
% 11.89/4.48  Inferencing          : 0.90
% 11.89/4.48  Reduction            : 0.95
% 11.89/4.48  Demodulation         : 0.62
% 11.89/4.48  BG Simplification    : 0.10
% 11.89/4.48  Subsumption          : 0.66
% 11.89/4.48  Abstraction          : 0.11
% 11.89/4.48  MUC search           : 0.00
% 11.89/4.48  Cooper               : 0.00
% 11.89/4.48  Total                : 3.73
% 11.89/4.48  Index Insertion      : 0.00
% 11.89/4.48  Index Deletion       : 0.00
% 11.89/4.48  Index Matching       : 0.00
% 11.89/4.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
