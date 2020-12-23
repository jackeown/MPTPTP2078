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
% DateTime   : Thu Dec  3 10:06:46 EST 2020

% Result     : Theorem 13.98s
% Output     : CNFRefutation 14.18s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 223 expanded)
%              Number of leaves         :   34 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 ( 661 expanded)
%              Number of equality atoms :   16 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_4 > #skF_11 > #skF_10 > #skF_2 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_6 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) )
         => ( r2_hidden(k4_tarski(A,B),C)
          <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> ! [B,C] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r2_hidden(C,k3_relat_1(A))
              & B != C
              & ~ r2_hidden(k4_tarski(B,C),A)
              & ~ r2_hidden(k4_tarski(C,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_115,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ( v2_wellord1(B)
          & r1_tarski(A,k3_relat_1(B)) )
       => ( ~ ( A != k3_relat_1(B)
              & ! [C] :
                  ~ ( r2_hidden(C,k3_relat_1(B))
                    & A = k1_wellord1(B,C) ) )
        <=> ! [C] :
              ( r2_hidden(C,A)
             => ! [D] :
                  ( r2_hidden(k4_tarski(D,C),B)
                 => r2_hidden(D,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_wellord1)).

tff(c_80,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_78,plain,(
    v2_wellord1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_89,plain,(
    ! [A_47] :
      ( v1_relat_2(A_47)
      | ~ v2_wellord1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,
    ( v1_relat_2('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_78,c_89])).

tff(c_95,plain,(
    v1_relat_2('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_92])).

tff(c_76,plain,(
    r2_hidden('#skF_10',k3_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    ! [B_22,A_19] :
      ( r2_hidden(k4_tarski(B_22,B_22),A_19)
      | ~ r2_hidden(B_22,k3_relat_1(A_19))
      | ~ v1_relat_2(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_88,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_12')
    | r1_tarski(k1_wellord1('#skF_12','#skF_10'),k1_wellord1('#skF_12','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_104,plain,(
    r1_tarski(k1_wellord1('#skF_12','#skF_10'),k1_wellord1('#skF_12','#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_30,plain,(
    ! [A_18] :
      ( v6_relat_2(A_18)
      | ~ v2_wellord1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_74,plain,(
    r2_hidden('#skF_11',k3_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_7150,plain,(
    ! [C_507,B_508,A_509] :
      ( r2_hidden(k4_tarski(C_507,B_508),A_509)
      | r2_hidden(k4_tarski(B_508,C_507),A_509)
      | C_507 = B_508
      | ~ r2_hidden(C_507,k3_relat_1(A_509))
      | ~ r2_hidden(B_508,k3_relat_1(A_509))
      | ~ v6_relat_2(A_509)
      | ~ v1_relat_1(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [D_17,A_6,B_13] :
      ( r2_hidden(D_17,k1_wellord1(A_6,B_13))
      | ~ r2_hidden(k4_tarski(D_17,B_13),A_6)
      | D_17 = B_13
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11708,plain,(
    ! [C_737,A_738,B_739] :
      ( r2_hidden(C_737,k1_wellord1(A_738,B_739))
      | r2_hidden(k4_tarski(B_739,C_737),A_738)
      | C_737 = B_739
      | ~ r2_hidden(C_737,k3_relat_1(A_738))
      | ~ r2_hidden(B_739,k3_relat_1(A_738))
      | ~ v6_relat_2(A_738)
      | ~ v1_relat_1(A_738) ) ),
    inference(resolution,[status(thm)],[c_7150,c_8])).

tff(c_82,plain,
    ( ~ r1_tarski(k1_wellord1('#skF_12','#skF_10'),k1_wellord1('#skF_12','#skF_11'))
    | ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_119,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_82])).

tff(c_11823,plain,
    ( r2_hidden('#skF_11',k1_wellord1('#skF_12','#skF_10'))
    | '#skF_11' = '#skF_10'
    | ~ r2_hidden('#skF_11',k3_relat_1('#skF_12'))
    | ~ r2_hidden('#skF_10',k3_relat_1('#skF_12'))
    | ~ v6_relat_2('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_11708,c_119])).

tff(c_11862,plain,
    ( r2_hidden('#skF_11',k1_wellord1('#skF_12','#skF_10'))
    | '#skF_11' = '#skF_10'
    | ~ v6_relat_2('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_11823])).

tff(c_11864,plain,(
    ~ v6_relat_2('#skF_12') ),
    inference(splitLeft,[status(thm)],[c_11862])).

tff(c_11870,plain,
    ( ~ v2_wellord1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_30,c_11864])).

tff(c_11877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_11870])).

tff(c_11878,plain,
    ( '#skF_11' = '#skF_10'
    | r2_hidden('#skF_11',k1_wellord1('#skF_12','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_11862])).

tff(c_12010,plain,(
    r2_hidden('#skF_11',k1_wellord1('#skF_12','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_11878])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12024,plain,(
    ! [B_744] :
      ( r2_hidden('#skF_11',B_744)
      | ~ r1_tarski(k1_wellord1('#skF_12','#skF_10'),B_744) ) ),
    inference(resolution,[status(thm)],[c_12010,c_2])).

tff(c_12092,plain,(
    r2_hidden('#skF_11',k1_wellord1('#skF_12','#skF_11')) ),
    inference(resolution,[status(thm)],[c_104,c_12024])).

tff(c_12,plain,(
    ! [D_17,A_6] :
      ( ~ r2_hidden(D_17,k1_wellord1(A_6,D_17))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12102,plain,(
    ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_12092,c_12])).

tff(c_12112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12102])).

tff(c_12113,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_11878])).

tff(c_12191,plain,(
    ~ r2_hidden(k4_tarski('#skF_10','#skF_10'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12113,c_119])).

tff(c_12235,plain,
    ( ~ r2_hidden('#skF_10',k3_relat_1('#skF_12'))
    | ~ v1_relat_2('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_38,c_12191])).

tff(c_12247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_95,c_76,c_12235])).

tff(c_12248,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_12251,plain,(
    ~ r1_tarski(k1_wellord1('#skF_12','#skF_10'),k1_wellord1('#skF_12','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12248,c_82])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [D_17,B_13,A_6] :
      ( r2_hidden(k4_tarski(D_17,B_13),A_6)
      | ~ r2_hidden(D_17,k1_wellord1(A_6,B_13))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12258,plain,(
    ! [A_757,B_758] :
      ( ~ r2_hidden('#skF_1'(A_757,B_758),B_758)
      | r1_tarski(A_757,B_758) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12263,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_12258])).

tff(c_72,plain,(
    ! [D_45,B_33,C_43] :
      ( r2_hidden(D_45,k3_relat_1(B_33))
      | ~ r2_hidden(k4_tarski(D_45,C_43),B_33)
      | ~ r2_hidden(C_43,k3_relat_1(B_33))
      | ~ r1_tarski(k3_relat_1(B_33),k3_relat_1(B_33))
      | ~ v2_wellord1(B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12649,plain,(
    ! [D_869,B_870,C_871] :
      ( r2_hidden(D_869,k3_relat_1(B_870))
      | ~ r2_hidden(k4_tarski(D_869,C_871),B_870)
      | ~ r2_hidden(C_871,k3_relat_1(B_870))
      | ~ v2_wellord1(B_870)
      | ~ v1_relat_1(B_870) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12263,c_72])).

tff(c_12723,plain,(
    ! [D_880,A_881,B_882] :
      ( r2_hidden(D_880,k3_relat_1(A_881))
      | ~ r2_hidden(B_882,k3_relat_1(A_881))
      | ~ v2_wellord1(A_881)
      | ~ r2_hidden(D_880,k1_wellord1(A_881,B_882))
      | ~ v1_relat_1(A_881) ) ),
    inference(resolution,[status(thm)],[c_10,c_12649])).

tff(c_12776,plain,(
    ! [D_880] :
      ( r2_hidden(D_880,k3_relat_1('#skF_12'))
      | ~ v2_wellord1('#skF_12')
      | ~ r2_hidden(D_880,k1_wellord1('#skF_12','#skF_11'))
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_74,c_12723])).

tff(c_12804,plain,(
    ! [D_883] :
      ( r2_hidden(D_883,k3_relat_1('#skF_12'))
      | ~ r2_hidden(D_883,k1_wellord1('#skF_12','#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_12776])).

tff(c_12959,plain,(
    ! [B_888] :
      ( r2_hidden('#skF_1'(k1_wellord1('#skF_12','#skF_11'),B_888),k3_relat_1('#skF_12'))
      | r1_tarski(k1_wellord1('#skF_12','#skF_11'),B_888) ) ),
    inference(resolution,[status(thm)],[c_6,c_12804])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12972,plain,(
    r1_tarski(k1_wellord1('#skF_12','#skF_11'),k3_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_12959,c_4])).

tff(c_12427,plain,(
    ! [D_805,A_806,B_807] :
      ( r2_hidden(D_805,k1_wellord1(A_806,B_807))
      | ~ r2_hidden(k4_tarski(D_805,B_807),A_806)
      | D_805 = B_807
      | ~ v1_relat_1(A_806) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12439,plain,
    ( r2_hidden('#skF_10',k1_wellord1('#skF_12','#skF_11'))
    | '#skF_11' = '#skF_10'
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_12248,c_12427])).

tff(c_12446,plain,
    ( r2_hidden('#skF_10',k1_wellord1('#skF_12','#skF_11'))
    | '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_12439])).

tff(c_12447,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_12446])).

tff(c_12454,plain,(
    ~ r1_tarski(k1_wellord1('#skF_12','#skF_10'),k1_wellord1('#skF_12','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12447,c_12251])).

tff(c_12459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12263,c_12454])).

tff(c_12460,plain,(
    r2_hidden('#skF_10',k1_wellord1('#skF_12','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_12446])).

tff(c_14491,plain,(
    ! [C_984,B_985,D_986,C_987] :
      ( ~ r2_hidden(C_984,k3_relat_1(B_985))
      | r2_hidden(D_986,k1_wellord1(B_985,C_984))
      | ~ r2_hidden(k4_tarski(D_986,C_987),B_985)
      | ~ r2_hidden(C_987,k1_wellord1(B_985,C_984))
      | ~ r1_tarski(k1_wellord1(B_985,C_984),k3_relat_1(B_985))
      | ~ v2_wellord1(B_985)
      | ~ v1_relat_1(B_985) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_21401,plain,(
    ! [C_1228,A_1229,D_1230,B_1231] :
      ( ~ r2_hidden(C_1228,k3_relat_1(A_1229))
      | r2_hidden(D_1230,k1_wellord1(A_1229,C_1228))
      | ~ r2_hidden(B_1231,k1_wellord1(A_1229,C_1228))
      | ~ r1_tarski(k1_wellord1(A_1229,C_1228),k3_relat_1(A_1229))
      | ~ v2_wellord1(A_1229)
      | ~ r2_hidden(D_1230,k1_wellord1(A_1229,B_1231))
      | ~ v1_relat_1(A_1229) ) ),
    inference(resolution,[status(thm)],[c_10,c_14491])).

tff(c_21528,plain,(
    ! [D_1230] :
      ( ~ r2_hidden('#skF_11',k3_relat_1('#skF_12'))
      | r2_hidden(D_1230,k1_wellord1('#skF_12','#skF_11'))
      | ~ r1_tarski(k1_wellord1('#skF_12','#skF_11'),k3_relat_1('#skF_12'))
      | ~ v2_wellord1('#skF_12')
      | ~ r2_hidden(D_1230,k1_wellord1('#skF_12','#skF_10'))
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_12460,c_21401])).

tff(c_21608,plain,(
    ! [D_1232] :
      ( r2_hidden(D_1232,k1_wellord1('#skF_12','#skF_11'))
      | ~ r2_hidden(D_1232,k1_wellord1('#skF_12','#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_12972,c_74,c_21528])).

tff(c_22023,plain,(
    ! [A_1239] :
      ( r1_tarski(A_1239,k1_wellord1('#skF_12','#skF_11'))
      | ~ r2_hidden('#skF_1'(A_1239,k1_wellord1('#skF_12','#skF_11')),k1_wellord1('#skF_12','#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_21608,c_4])).

tff(c_22055,plain,(
    r1_tarski(k1_wellord1('#skF_12','#skF_10'),k1_wellord1('#skF_12','#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_22023])).

tff(c_22068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12251,c_12251,c_22055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.98/5.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.98/5.59  
% 13.98/5.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.98/5.59  %$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_4 > #skF_11 > #skF_10 > #skF_2 > #skF_8 > #skF_3 > #skF_7 > #skF_1 > #skF_9 > #skF_6 > #skF_12
% 13.98/5.59  
% 13.98/5.59  %Foreground sorts:
% 13.98/5.59  
% 13.98/5.59  
% 13.98/5.59  %Background operators:
% 13.98/5.59  
% 13.98/5.59  
% 13.98/5.59  %Foreground operators:
% 13.98/5.59  tff('#skF_5', type, '#skF_5': $i > $i).
% 13.98/5.59  tff('#skF_4', type, '#skF_4': $i > $i).
% 13.98/5.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.98/5.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.98/5.59  tff('#skF_11', type, '#skF_11': $i).
% 13.98/5.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.98/5.59  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 13.98/5.59  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 13.98/5.59  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 13.98/5.59  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 13.98/5.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.98/5.59  tff('#skF_10', type, '#skF_10': $i).
% 13.98/5.59  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 13.98/5.59  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 13.98/5.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.98/5.59  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 13.98/5.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.98/5.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.98/5.59  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 13.98/5.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.98/5.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.98/5.59  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 13.98/5.59  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 13.98/5.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.98/5.59  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 13.98/5.59  tff('#skF_6', type, '#skF_6': $i > $i).
% 13.98/5.59  tff('#skF_12', type, '#skF_12': $i).
% 13.98/5.59  
% 14.18/5.61  tff(f_128, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 14.18/5.61  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 14.18/5.61  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> (![B]: (r2_hidden(B, k3_relat_1(A)) => r2_hidden(k4_tarski(B, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 14.18/5.61  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 14.18/5.61  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 14.18/5.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 14.18/5.61  tff(f_115, axiom, (![A, B]: (v1_relat_1(B) => ((v2_wellord1(B) & r1_tarski(A, k3_relat_1(B))) => (~(~(A = k3_relat_1(B)) & (![C]: ~(r2_hidden(C, k3_relat_1(B)) & (A = k1_wellord1(B, C))))) <=> (![C]: (r2_hidden(C, A) => (![D]: (r2_hidden(k4_tarski(D, C), B) => r2_hidden(D, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_wellord1)).
% 14.18/5.61  tff(c_80, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.18/5.61  tff(c_78, plain, (v2_wellord1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.18/5.61  tff(c_89, plain, (![A_47]: (v1_relat_2(A_47) | ~v2_wellord1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.18/5.61  tff(c_92, plain, (v1_relat_2('#skF_12') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_78, c_89])).
% 14.18/5.61  tff(c_95, plain, (v1_relat_2('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_92])).
% 14.18/5.61  tff(c_76, plain, (r2_hidden('#skF_10', k3_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.18/5.61  tff(c_38, plain, (![B_22, A_19]: (r2_hidden(k4_tarski(B_22, B_22), A_19) | ~r2_hidden(B_22, k3_relat_1(A_19)) | ~v1_relat_2(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.18/5.61  tff(c_88, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_12') | r1_tarski(k1_wellord1('#skF_12', '#skF_10'), k1_wellord1('#skF_12', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.18/5.61  tff(c_104, plain, (r1_tarski(k1_wellord1('#skF_12', '#skF_10'), k1_wellord1('#skF_12', '#skF_11'))), inference(splitLeft, [status(thm)], [c_88])).
% 14.18/5.61  tff(c_30, plain, (![A_18]: (v6_relat_2(A_18) | ~v2_wellord1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.18/5.61  tff(c_74, plain, (r2_hidden('#skF_11', k3_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.18/5.61  tff(c_7150, plain, (![C_507, B_508, A_509]: (r2_hidden(k4_tarski(C_507, B_508), A_509) | r2_hidden(k4_tarski(B_508, C_507), A_509) | C_507=B_508 | ~r2_hidden(C_507, k3_relat_1(A_509)) | ~r2_hidden(B_508, k3_relat_1(A_509)) | ~v6_relat_2(A_509) | ~v1_relat_1(A_509))), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.18/5.61  tff(c_8, plain, (![D_17, A_6, B_13]: (r2_hidden(D_17, k1_wellord1(A_6, B_13)) | ~r2_hidden(k4_tarski(D_17, B_13), A_6) | D_17=B_13 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.18/5.61  tff(c_11708, plain, (![C_737, A_738, B_739]: (r2_hidden(C_737, k1_wellord1(A_738, B_739)) | r2_hidden(k4_tarski(B_739, C_737), A_738) | C_737=B_739 | ~r2_hidden(C_737, k3_relat_1(A_738)) | ~r2_hidden(B_739, k3_relat_1(A_738)) | ~v6_relat_2(A_738) | ~v1_relat_1(A_738))), inference(resolution, [status(thm)], [c_7150, c_8])).
% 14.18/5.61  tff(c_82, plain, (~r1_tarski(k1_wellord1('#skF_12', '#skF_10'), k1_wellord1('#skF_12', '#skF_11')) | ~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.18/5.61  tff(c_119, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_82])).
% 14.18/5.61  tff(c_11823, plain, (r2_hidden('#skF_11', k1_wellord1('#skF_12', '#skF_10')) | '#skF_11'='#skF_10' | ~r2_hidden('#skF_11', k3_relat_1('#skF_12')) | ~r2_hidden('#skF_10', k3_relat_1('#skF_12')) | ~v6_relat_2('#skF_12') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_11708, c_119])).
% 14.18/5.61  tff(c_11862, plain, (r2_hidden('#skF_11', k1_wellord1('#skF_12', '#skF_10')) | '#skF_11'='#skF_10' | ~v6_relat_2('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_11823])).
% 14.18/5.61  tff(c_11864, plain, (~v6_relat_2('#skF_12')), inference(splitLeft, [status(thm)], [c_11862])).
% 14.18/5.61  tff(c_11870, plain, (~v2_wellord1('#skF_12') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_30, c_11864])).
% 14.18/5.61  tff(c_11877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_11870])).
% 14.18/5.61  tff(c_11878, plain, ('#skF_11'='#skF_10' | r2_hidden('#skF_11', k1_wellord1('#skF_12', '#skF_10'))), inference(splitRight, [status(thm)], [c_11862])).
% 14.18/5.61  tff(c_12010, plain, (r2_hidden('#skF_11', k1_wellord1('#skF_12', '#skF_10'))), inference(splitLeft, [status(thm)], [c_11878])).
% 14.18/5.61  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.18/5.61  tff(c_12024, plain, (![B_744]: (r2_hidden('#skF_11', B_744) | ~r1_tarski(k1_wellord1('#skF_12', '#skF_10'), B_744))), inference(resolution, [status(thm)], [c_12010, c_2])).
% 14.18/5.61  tff(c_12092, plain, (r2_hidden('#skF_11', k1_wellord1('#skF_12', '#skF_11'))), inference(resolution, [status(thm)], [c_104, c_12024])).
% 14.18/5.61  tff(c_12, plain, (![D_17, A_6]: (~r2_hidden(D_17, k1_wellord1(A_6, D_17)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.18/5.61  tff(c_12102, plain, (~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_12092, c_12])).
% 14.18/5.61  tff(c_12112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_12102])).
% 14.18/5.61  tff(c_12113, plain, ('#skF_11'='#skF_10'), inference(splitRight, [status(thm)], [c_11878])).
% 14.18/5.61  tff(c_12191, plain, (~r2_hidden(k4_tarski('#skF_10', '#skF_10'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_12113, c_119])).
% 14.18/5.61  tff(c_12235, plain, (~r2_hidden('#skF_10', k3_relat_1('#skF_12')) | ~v1_relat_2('#skF_12') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_38, c_12191])).
% 14.18/5.61  tff(c_12247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_95, c_76, c_12235])).
% 14.18/5.61  tff(c_12248, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_12')), inference(splitRight, [status(thm)], [c_88])).
% 14.18/5.61  tff(c_12251, plain, (~r1_tarski(k1_wellord1('#skF_12', '#skF_10'), k1_wellord1('#skF_12', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_12248, c_82])).
% 14.18/5.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.18/5.61  tff(c_10, plain, (![D_17, B_13, A_6]: (r2_hidden(k4_tarski(D_17, B_13), A_6) | ~r2_hidden(D_17, k1_wellord1(A_6, B_13)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.18/5.61  tff(c_12258, plain, (![A_757, B_758]: (~r2_hidden('#skF_1'(A_757, B_758), B_758) | r1_tarski(A_757, B_758))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.18/5.61  tff(c_12263, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_12258])).
% 14.18/5.61  tff(c_72, plain, (![D_45, B_33, C_43]: (r2_hidden(D_45, k3_relat_1(B_33)) | ~r2_hidden(k4_tarski(D_45, C_43), B_33) | ~r2_hidden(C_43, k3_relat_1(B_33)) | ~r1_tarski(k3_relat_1(B_33), k3_relat_1(B_33)) | ~v2_wellord1(B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.18/5.61  tff(c_12649, plain, (![D_869, B_870, C_871]: (r2_hidden(D_869, k3_relat_1(B_870)) | ~r2_hidden(k4_tarski(D_869, C_871), B_870) | ~r2_hidden(C_871, k3_relat_1(B_870)) | ~v2_wellord1(B_870) | ~v1_relat_1(B_870))), inference(demodulation, [status(thm), theory('equality')], [c_12263, c_72])).
% 14.18/5.61  tff(c_12723, plain, (![D_880, A_881, B_882]: (r2_hidden(D_880, k3_relat_1(A_881)) | ~r2_hidden(B_882, k3_relat_1(A_881)) | ~v2_wellord1(A_881) | ~r2_hidden(D_880, k1_wellord1(A_881, B_882)) | ~v1_relat_1(A_881))), inference(resolution, [status(thm)], [c_10, c_12649])).
% 14.18/5.61  tff(c_12776, plain, (![D_880]: (r2_hidden(D_880, k3_relat_1('#skF_12')) | ~v2_wellord1('#skF_12') | ~r2_hidden(D_880, k1_wellord1('#skF_12', '#skF_11')) | ~v1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_74, c_12723])).
% 14.18/5.61  tff(c_12804, plain, (![D_883]: (r2_hidden(D_883, k3_relat_1('#skF_12')) | ~r2_hidden(D_883, k1_wellord1('#skF_12', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_12776])).
% 14.18/5.61  tff(c_12959, plain, (![B_888]: (r2_hidden('#skF_1'(k1_wellord1('#skF_12', '#skF_11'), B_888), k3_relat_1('#skF_12')) | r1_tarski(k1_wellord1('#skF_12', '#skF_11'), B_888))), inference(resolution, [status(thm)], [c_6, c_12804])).
% 14.18/5.61  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.18/5.61  tff(c_12972, plain, (r1_tarski(k1_wellord1('#skF_12', '#skF_11'), k3_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_12959, c_4])).
% 14.18/5.61  tff(c_12427, plain, (![D_805, A_806, B_807]: (r2_hidden(D_805, k1_wellord1(A_806, B_807)) | ~r2_hidden(k4_tarski(D_805, B_807), A_806) | D_805=B_807 | ~v1_relat_1(A_806))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.18/5.61  tff(c_12439, plain, (r2_hidden('#skF_10', k1_wellord1('#skF_12', '#skF_11')) | '#skF_11'='#skF_10' | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_12248, c_12427])).
% 14.18/5.61  tff(c_12446, plain, (r2_hidden('#skF_10', k1_wellord1('#skF_12', '#skF_11')) | '#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_12439])).
% 14.18/5.61  tff(c_12447, plain, ('#skF_11'='#skF_10'), inference(splitLeft, [status(thm)], [c_12446])).
% 14.18/5.61  tff(c_12454, plain, (~r1_tarski(k1_wellord1('#skF_12', '#skF_10'), k1_wellord1('#skF_12', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_12447, c_12251])).
% 14.18/5.61  tff(c_12459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12263, c_12454])).
% 14.18/5.61  tff(c_12460, plain, (r2_hidden('#skF_10', k1_wellord1('#skF_12', '#skF_11'))), inference(splitRight, [status(thm)], [c_12446])).
% 14.18/5.61  tff(c_14491, plain, (![C_984, B_985, D_986, C_987]: (~r2_hidden(C_984, k3_relat_1(B_985)) | r2_hidden(D_986, k1_wellord1(B_985, C_984)) | ~r2_hidden(k4_tarski(D_986, C_987), B_985) | ~r2_hidden(C_987, k1_wellord1(B_985, C_984)) | ~r1_tarski(k1_wellord1(B_985, C_984), k3_relat_1(B_985)) | ~v2_wellord1(B_985) | ~v1_relat_1(B_985))), inference(cnfTransformation, [status(thm)], [f_115])).
% 14.18/5.61  tff(c_21401, plain, (![C_1228, A_1229, D_1230, B_1231]: (~r2_hidden(C_1228, k3_relat_1(A_1229)) | r2_hidden(D_1230, k1_wellord1(A_1229, C_1228)) | ~r2_hidden(B_1231, k1_wellord1(A_1229, C_1228)) | ~r1_tarski(k1_wellord1(A_1229, C_1228), k3_relat_1(A_1229)) | ~v2_wellord1(A_1229) | ~r2_hidden(D_1230, k1_wellord1(A_1229, B_1231)) | ~v1_relat_1(A_1229))), inference(resolution, [status(thm)], [c_10, c_14491])).
% 14.18/5.61  tff(c_21528, plain, (![D_1230]: (~r2_hidden('#skF_11', k3_relat_1('#skF_12')) | r2_hidden(D_1230, k1_wellord1('#skF_12', '#skF_11')) | ~r1_tarski(k1_wellord1('#skF_12', '#skF_11'), k3_relat_1('#skF_12')) | ~v2_wellord1('#skF_12') | ~r2_hidden(D_1230, k1_wellord1('#skF_12', '#skF_10')) | ~v1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_12460, c_21401])).
% 14.18/5.61  tff(c_21608, plain, (![D_1232]: (r2_hidden(D_1232, k1_wellord1('#skF_12', '#skF_11')) | ~r2_hidden(D_1232, k1_wellord1('#skF_12', '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_12972, c_74, c_21528])).
% 14.18/5.61  tff(c_22023, plain, (![A_1239]: (r1_tarski(A_1239, k1_wellord1('#skF_12', '#skF_11')) | ~r2_hidden('#skF_1'(A_1239, k1_wellord1('#skF_12', '#skF_11')), k1_wellord1('#skF_12', '#skF_10')))), inference(resolution, [status(thm)], [c_21608, c_4])).
% 14.18/5.61  tff(c_22055, plain, (r1_tarski(k1_wellord1('#skF_12', '#skF_10'), k1_wellord1('#skF_12', '#skF_11'))), inference(resolution, [status(thm)], [c_6, c_22023])).
% 14.18/5.61  tff(c_22068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12251, c_12251, c_22055])).
% 14.18/5.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.18/5.61  
% 14.18/5.61  Inference rules
% 14.18/5.61  ----------------------
% 14.18/5.61  #Ref     : 0
% 14.18/5.61  #Sup     : 4740
% 14.18/5.61  #Fact    : 6
% 14.18/5.61  #Define  : 0
% 14.18/5.61  #Split   : 34
% 14.18/5.61  #Chain   : 0
% 14.18/5.61  #Close   : 0
% 14.18/5.61  
% 14.18/5.61  Ordering : KBO
% 14.18/5.61  
% 14.18/5.61  Simplification rules
% 14.18/5.62  ----------------------
% 14.18/5.62  #Subsume      : 1310
% 14.18/5.62  #Demod        : 959
% 14.18/5.62  #Tautology    : 272
% 14.18/5.62  #SimpNegUnit  : 30
% 14.18/5.62  #BackRed      : 189
% 14.18/5.62  
% 14.18/5.62  #Partial instantiations: 0
% 14.18/5.62  #Strategies tried      : 1
% 14.18/5.62  
% 14.18/5.62  Timing (in seconds)
% 14.18/5.62  ----------------------
% 14.18/5.62  Preprocessing        : 0.36
% 14.18/5.62  Parsing              : 0.18
% 14.18/5.62  CNF conversion       : 0.03
% 14.18/5.62  Main loop            : 4.41
% 14.18/5.62  Inferencing          : 1.05
% 14.18/5.62  Reduction            : 0.98
% 14.18/5.62  Demodulation         : 0.63
% 14.18/5.62  BG Simplification    : 0.12
% 14.18/5.62  Subsumption          : 1.96
% 14.18/5.62  Abstraction          : 0.20
% 14.18/5.62  MUC search           : 0.00
% 14.18/5.62  Cooper               : 0.00
% 14.18/5.62  Total                : 4.81
% 14.18/5.62  Index Insertion      : 0.00
% 14.18/5.62  Index Deletion       : 0.00
% 14.18/5.62  Index Matching       : 0.00
% 14.18/5.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
