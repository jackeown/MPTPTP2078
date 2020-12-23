%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:06 EST 2020

% Result     : Theorem 49.48s
% Output     : CNFRefutation 49.48s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 113 expanded)
%              Number of leaves         :   47 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 210 expanded)
%              Number of equality atoms :   29 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_110,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    k1_funct_1('#skF_11','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_74,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_186,plain,(
    ! [C_85,B_86,A_87] :
      ( v5_relat_1(C_85,B_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_195,plain,(
    v5_relat_1('#skF_11',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_74,c_186])).

tff(c_150,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_159,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_74,c_150])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k2_relat_1(B_23),A_22)
      | ~ v5_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_78,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_76,plain,(
    v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_470,plain,(
    ! [A_151,B_152,C_153] :
      ( k1_relset_1(A_151,B_152,C_153) = k1_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_479,plain,(
    k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_74,c_470])).

tff(c_1539,plain,(
    ! [B_257,A_258,C_259] :
      ( k1_xboole_0 = B_257
      | k1_relset_1(A_258,B_257,C_259) = A_258
      | ~ v1_funct_2(C_259,A_258,B_257)
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_258,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1546,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_74,c_1539])).

tff(c_1550,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_479,c_1546])).

tff(c_1551,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1550])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_775,plain,(
    ! [B_181,A_182] :
      ( r2_hidden(k1_funct_1(B_181,A_182),k2_relat_1(B_181))
      | ~ r2_hidden(A_182,k1_relat_1(B_181))
      | ~ v1_funct_1(B_181)
      | ~ v1_relat_1(B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [C_19,A_16,B_17] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10589,plain,(
    ! [B_381,A_382,A_383] :
      ( r2_hidden(k1_funct_1(B_381,A_382),A_383)
      | ~ m1_subset_1(k2_relat_1(B_381),k1_zfmisc_1(A_383))
      | ~ r2_hidden(A_382,k1_relat_1(B_381))
      | ~ v1_funct_1(B_381)
      | ~ v1_relat_1(B_381) ) ),
    inference(resolution,[status(thm)],[c_775,c_26])).

tff(c_27946,plain,(
    ! [B_668,A_669,B_670] :
      ( r2_hidden(k1_funct_1(B_668,A_669),B_670)
      | ~ r2_hidden(A_669,k1_relat_1(B_668))
      | ~ v1_funct_1(B_668)
      | ~ v1_relat_1(B_668)
      | ~ r1_tarski(k2_relat_1(B_668),B_670) ) ),
    inference(resolution,[status(thm)],[c_30,c_10589])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184234,plain,(
    ! [B_1765,A_1766,A_1767] :
      ( k1_funct_1(B_1765,A_1766) = A_1767
      | ~ r2_hidden(A_1766,k1_relat_1(B_1765))
      | ~ v1_funct_1(B_1765)
      | ~ v1_relat_1(B_1765)
      | ~ r1_tarski(k2_relat_1(B_1765),k1_tarski(A_1767)) ) ),
    inference(resolution,[status(thm)],[c_27946,c_8])).

tff(c_184496,plain,(
    ! [A_1766,A_1767] :
      ( k1_funct_1('#skF_11',A_1766) = A_1767
      | ~ r2_hidden(A_1766,'#skF_8')
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11')
      | ~ r1_tarski(k2_relat_1('#skF_11'),k1_tarski(A_1767)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1551,c_184234])).

tff(c_184602,plain,(
    ! [A_1768,A_1769] :
      ( k1_funct_1('#skF_11',A_1768) = A_1769
      | ~ r2_hidden(A_1768,'#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_11'),k1_tarski(A_1769)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_78,c_184496])).

tff(c_184789,plain,(
    ! [A_1770] :
      ( k1_funct_1('#skF_11','#skF_10') = A_1770
      | ~ r1_tarski(k2_relat_1('#skF_11'),k1_tarski(A_1770)) ) ),
    inference(resolution,[status(thm)],[c_72,c_184602])).

tff(c_184792,plain,(
    ! [A_1770] :
      ( k1_funct_1('#skF_11','#skF_10') = A_1770
      | ~ v5_relat_1('#skF_11',k1_tarski(A_1770))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_34,c_184789])).

tff(c_184796,plain,(
    ! [A_1771] :
      ( k1_funct_1('#skF_11','#skF_10') = A_1771
      | ~ v5_relat_1('#skF_11',k1_tarski(A_1771)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_184792])).

tff(c_184799,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_195,c_184796])).

tff(c_184803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_184799])).

tff(c_184804,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1550])).

tff(c_10,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [B_59,A_60] :
      ( ~ r2_hidden(B_59,A_60)
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [C_9] : ~ v1_xboole_0(k1_tarski(C_9)) ),
    inference(resolution,[status(thm)],[c_10,c_89])).

tff(c_184835,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_184804,c_96])).

tff(c_184843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_184835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 49.48/39.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 49.48/39.01  
% 49.48/39.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 49.48/39.01  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 49.48/39.01  
% 49.48/39.01  %Foreground sorts:
% 49.48/39.01  
% 49.48/39.01  
% 49.48/39.01  %Background operators:
% 49.48/39.01  
% 49.48/39.01  
% 49.48/39.01  %Foreground operators:
% 49.48/39.01  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 49.48/39.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 49.48/39.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 49.48/39.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 49.48/39.01  tff('#skF_11', type, '#skF_11': $i).
% 49.48/39.01  tff(k1_tarski, type, k1_tarski: $i > $i).
% 49.48/39.01  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 49.48/39.01  tff('#skF_1', type, '#skF_1': $i > $i).
% 49.48/39.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 49.48/39.01  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 49.48/39.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 49.48/39.01  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 49.48/39.01  tff('#skF_10', type, '#skF_10': $i).
% 49.48/39.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 49.48/39.01  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 49.48/39.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 49.48/39.01  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 49.48/39.01  tff('#skF_9', type, '#skF_9': $i).
% 49.48/39.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 49.48/39.01  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 49.48/39.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 49.48/39.01  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 49.48/39.01  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 49.48/39.01  tff('#skF_8', type, '#skF_8': $i).
% 49.48/39.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 49.48/39.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 49.48/39.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 49.48/39.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 49.48/39.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 49.48/39.01  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 49.48/39.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 49.48/39.01  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 49.48/39.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 49.48/39.01  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 49.48/39.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 49.48/39.01  
% 49.48/39.02  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 49.48/39.02  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 49.48/39.02  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 49.48/39.02  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 49.48/39.02  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 49.48/39.02  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 49.48/39.02  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 49.48/39.02  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 49.48/39.02  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 49.48/39.02  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 49.48/39.02  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 49.48/39.02  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 49.48/39.02  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 49.48/39.02  tff(c_70, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_121])).
% 49.48/39.02  tff(c_74, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 49.48/39.02  tff(c_186, plain, (![C_85, B_86, A_87]: (v5_relat_1(C_85, B_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 49.48/39.02  tff(c_195, plain, (v5_relat_1('#skF_11', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_74, c_186])).
% 49.48/39.02  tff(c_150, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 49.48/39.02  tff(c_159, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_74, c_150])).
% 49.48/39.02  tff(c_34, plain, (![B_23, A_22]: (r1_tarski(k2_relat_1(B_23), A_22) | ~v5_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 49.48/39.02  tff(c_72, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_121])).
% 49.48/39.02  tff(c_78, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_121])).
% 49.48/39.02  tff(c_76, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 49.48/39.02  tff(c_470, plain, (![A_151, B_152, C_153]: (k1_relset_1(A_151, B_152, C_153)=k1_relat_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 49.48/39.02  tff(c_479, plain, (k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_74, c_470])).
% 49.48/39.02  tff(c_1539, plain, (![B_257, A_258, C_259]: (k1_xboole_0=B_257 | k1_relset_1(A_258, B_257, C_259)=A_258 | ~v1_funct_2(C_259, A_258, B_257) | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_258, B_257))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 49.48/39.02  tff(c_1546, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_74, c_1539])).
% 49.48/39.02  tff(c_1550, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_479, c_1546])).
% 49.48/39.02  tff(c_1551, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_1550])).
% 49.48/39.02  tff(c_30, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 49.48/39.02  tff(c_775, plain, (![B_181, A_182]: (r2_hidden(k1_funct_1(B_181, A_182), k2_relat_1(B_181)) | ~r2_hidden(A_182, k1_relat_1(B_181)) | ~v1_funct_1(B_181) | ~v1_relat_1(B_181))), inference(cnfTransformation, [status(thm)], [f_78])).
% 49.48/39.02  tff(c_26, plain, (![C_19, A_16, B_17]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 49.48/39.02  tff(c_10589, plain, (![B_381, A_382, A_383]: (r2_hidden(k1_funct_1(B_381, A_382), A_383) | ~m1_subset_1(k2_relat_1(B_381), k1_zfmisc_1(A_383)) | ~r2_hidden(A_382, k1_relat_1(B_381)) | ~v1_funct_1(B_381) | ~v1_relat_1(B_381))), inference(resolution, [status(thm)], [c_775, c_26])).
% 49.48/39.02  tff(c_27946, plain, (![B_668, A_669, B_670]: (r2_hidden(k1_funct_1(B_668, A_669), B_670) | ~r2_hidden(A_669, k1_relat_1(B_668)) | ~v1_funct_1(B_668) | ~v1_relat_1(B_668) | ~r1_tarski(k2_relat_1(B_668), B_670))), inference(resolution, [status(thm)], [c_30, c_10589])).
% 49.48/39.02  tff(c_8, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 49.48/39.02  tff(c_184234, plain, (![B_1765, A_1766, A_1767]: (k1_funct_1(B_1765, A_1766)=A_1767 | ~r2_hidden(A_1766, k1_relat_1(B_1765)) | ~v1_funct_1(B_1765) | ~v1_relat_1(B_1765) | ~r1_tarski(k2_relat_1(B_1765), k1_tarski(A_1767)))), inference(resolution, [status(thm)], [c_27946, c_8])).
% 49.48/39.02  tff(c_184496, plain, (![A_1766, A_1767]: (k1_funct_1('#skF_11', A_1766)=A_1767 | ~r2_hidden(A_1766, '#skF_8') | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11') | ~r1_tarski(k2_relat_1('#skF_11'), k1_tarski(A_1767)))), inference(superposition, [status(thm), theory('equality')], [c_1551, c_184234])).
% 49.48/39.02  tff(c_184602, plain, (![A_1768, A_1769]: (k1_funct_1('#skF_11', A_1768)=A_1769 | ~r2_hidden(A_1768, '#skF_8') | ~r1_tarski(k2_relat_1('#skF_11'), k1_tarski(A_1769)))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_78, c_184496])).
% 49.48/39.02  tff(c_184789, plain, (![A_1770]: (k1_funct_1('#skF_11', '#skF_10')=A_1770 | ~r1_tarski(k2_relat_1('#skF_11'), k1_tarski(A_1770)))), inference(resolution, [status(thm)], [c_72, c_184602])).
% 49.48/39.02  tff(c_184792, plain, (![A_1770]: (k1_funct_1('#skF_11', '#skF_10')=A_1770 | ~v5_relat_1('#skF_11', k1_tarski(A_1770)) | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_34, c_184789])).
% 49.48/39.02  tff(c_184796, plain, (![A_1771]: (k1_funct_1('#skF_11', '#skF_10')=A_1771 | ~v5_relat_1('#skF_11', k1_tarski(A_1771)))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_184792])).
% 49.48/39.02  tff(c_184799, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_195, c_184796])).
% 49.48/39.02  tff(c_184803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_184799])).
% 49.48/39.02  tff(c_184804, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1550])).
% 49.48/39.02  tff(c_10, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 49.48/39.02  tff(c_89, plain, (![B_59, A_60]: (~r2_hidden(B_59, A_60) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 49.48/39.02  tff(c_96, plain, (![C_9]: (~v1_xboole_0(k1_tarski(C_9)))), inference(resolution, [status(thm)], [c_10, c_89])).
% 49.48/39.02  tff(c_184835, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_184804, c_96])).
% 49.48/39.02  tff(c_184843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_184835])).
% 49.48/39.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 49.48/39.02  
% 49.48/39.02  Inference rules
% 49.48/39.02  ----------------------
% 49.48/39.02  #Ref     : 0
% 49.48/39.02  #Sup     : 53818
% 49.48/39.02  #Fact    : 0
% 49.48/39.02  #Define  : 0
% 49.48/39.02  #Split   : 77
% 49.48/39.02  #Chain   : 0
% 49.48/39.02  #Close   : 0
% 49.48/39.02  
% 49.48/39.02  Ordering : KBO
% 49.48/39.02  
% 49.48/39.02  Simplification rules
% 49.48/39.02  ----------------------
% 49.48/39.02  #Subsume      : 34225
% 49.48/39.02  #Demod        : 31650
% 49.48/39.02  #Tautology    : 5616
% 49.48/39.02  #SimpNegUnit  : 1079
% 49.48/39.02  #BackRed      : 224
% 49.48/39.02  
% 49.48/39.02  #Partial instantiations: 0
% 49.48/39.02  #Strategies tried      : 1
% 49.48/39.02  
% 49.48/39.02  Timing (in seconds)
% 49.48/39.02  ----------------------
% 49.48/39.03  Preprocessing        : 0.50
% 49.48/39.03  Parsing              : 0.27
% 49.48/39.03  CNF conversion       : 0.04
% 49.48/39.03  Main loop            : 37.65
% 49.48/39.03  Inferencing          : 3.00
% 49.48/39.03  Reduction            : 6.87
% 49.48/39.03  Demodulation         : 4.59
% 49.48/39.03  BG Simplification    : 0.29
% 49.48/39.03  Subsumption          : 25.90
% 49.48/39.03  Abstraction          : 0.66
% 49.48/39.03  MUC search           : 0.00
% 49.48/39.03  Cooper               : 0.00
% 49.48/39.03  Total                : 38.19
% 49.48/39.03  Index Insertion      : 0.00
% 49.48/39.03  Index Deletion       : 0.00
% 49.48/39.03  Index Matching       : 0.00
% 49.48/39.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
