%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:09 EST 2020

% Result     : Theorem 13.70s
% Output     : CNFRefutation 13.75s
% Verified   : 
% Statistics : Number of formulae       :  297 (2372 expanded)
%              Number of leaves         :   44 ( 776 expanded)
%              Depth                    :   17
%              Number of atoms          :  536 (6347 expanded)
%              Number of equality atoms :  192 (2290 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_106,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_36,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_30705,plain,(
    ! [B_1876,A_1877] :
      ( v1_relat_1(B_1876)
      | ~ m1_subset_1(B_1876,k1_zfmisc_1(A_1877))
      | ~ v1_relat_1(A_1877) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30717,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_30705])).

tff(c_30727,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30717])).

tff(c_30942,plain,(
    ! [C_1897,A_1898,B_1899] :
      ( v4_relat_1(C_1897,A_1898)
      | ~ m1_subset_1(C_1897,k1_zfmisc_1(k2_zfmisc_1(A_1898,B_1899))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30965,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_30942])).

tff(c_34,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_31064,plain,(
    ! [A_1912,B_1913,C_1914] :
      ( k2_relset_1(A_1912,B_1913,C_1914) = k2_relat_1(C_1914)
      | ~ m1_subset_1(C_1914,k1_zfmisc_1(k2_zfmisc_1(A_1912,B_1913))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_31089,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_31064])).

tff(c_74,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_31103,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31089,c_74])).

tff(c_31650,plain,(
    ! [C_1979,A_1980,B_1981] :
      ( m1_subset_1(C_1979,k1_zfmisc_1(k2_zfmisc_1(A_1980,B_1981)))
      | ~ r1_tarski(k2_relat_1(C_1979),B_1981)
      | ~ r1_tarski(k1_relat_1(C_1979),A_1980)
      | ~ v1_relat_1(C_1979) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_13755,plain,(
    ! [A_900,B_901,C_902] :
      ( k1_relset_1(A_900,B_901,C_902) = k1_relat_1(C_902)
      | ~ m1_subset_1(C_902,k1_zfmisc_1(k2_zfmisc_1(A_900,B_901))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_13780,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_13755])).

tff(c_14080,plain,(
    ! [B_938,A_939,C_940] :
      ( k1_xboole_0 = B_938
      | k1_relset_1(A_939,B_938,C_940) = A_939
      | ~ v1_funct_2(C_940,A_939,B_938)
      | ~ m1_subset_1(C_940,k1_zfmisc_1(k2_zfmisc_1(A_939,B_938))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_14096,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_14080])).

tff(c_14110,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_13780,c_14096])).

tff(c_14111,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_14110])).

tff(c_191,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_203,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_191])).

tff(c_213,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_203])).

tff(c_13647,plain,(
    ! [A_891,B_892,C_893] :
      ( k2_relset_1(A_891,B_892,C_893) = k2_relat_1(C_893)
      | ~ m1_subset_1(C_893,k1_zfmisc_1(k2_zfmisc_1(A_891,B_892))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_13672,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_13647])).

tff(c_13689,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13672,c_74])).

tff(c_13863,plain,(
    ! [C_914,A_915,B_916] :
      ( m1_subset_1(C_914,k1_zfmisc_1(k2_zfmisc_1(A_915,B_916)))
      | ~ r1_tarski(k2_relat_1(C_914),B_916)
      | ~ r1_tarski(k1_relat_1(C_914),A_915)
      | ~ v1_relat_1(C_914) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18276,plain,(
    ! [C_1112,A_1113,B_1114] :
      ( r1_tarski(C_1112,k2_zfmisc_1(A_1113,B_1114))
      | ~ r1_tarski(k2_relat_1(C_1112),B_1114)
      | ~ r1_tarski(k1_relat_1(C_1112),A_1113)
      | ~ v1_relat_1(C_1112) ) ),
    inference(resolution,[status(thm)],[c_13863,c_26])).

tff(c_18278,plain,(
    ! [A_1113] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_1113,'#skF_5'))
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_1113)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_13689,c_18276])).

tff(c_18302,plain,(
    ! [A_1115] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_1115,'#skF_5'))
      | ~ r1_tarski('#skF_3',A_1115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_14111,c_18278])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_13779,plain,(
    ! [A_900,B_901,A_14] :
      ( k1_relset_1(A_900,B_901,A_14) = k1_relat_1(A_14)
      | ~ r1_tarski(A_14,k2_zfmisc_1(A_900,B_901)) ) ),
    inference(resolution,[status(thm)],[c_28,c_13755])).

tff(c_18310,plain,(
    ! [A_1115] :
      ( k1_relset_1(A_1115,'#skF_5','#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_3',A_1115) ) ),
    inference(resolution,[status(thm)],[c_18302,c_13779])).

tff(c_18606,plain,(
    ! [A_1125] :
      ( k1_relset_1(A_1125,'#skF_5','#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_1125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14111,c_18310])).

tff(c_18626,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_18606])).

tff(c_44,plain,(
    ! [A_24] : k2_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56,plain,(
    ! [A_37] : m1_subset_1(k6_relat_1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_197,plain,(
    ! [A_37] :
      ( v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(k2_zfmisc_1(A_37,A_37)) ) ),
    inference(resolution,[status(thm)],[c_56,c_191])).

tff(c_222,plain,(
    ! [A_60] : v1_relat_1(k6_relat_1(A_60)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_197])).

tff(c_38,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_228,plain,(
    ! [A_60] :
      ( k2_relat_1(k6_relat_1(A_60)) != k1_xboole_0
      | k6_relat_1(A_60) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_222,c_38])).

tff(c_234,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_228])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_153,plain,(
    ! [A_54] : m1_subset_1(k6_relat_1(A_54),k1_zfmisc_1(k2_zfmisc_1(A_54,A_54))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_157,plain,(
    m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_153])).

tff(c_236,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_157])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_13261,plain,(
    ! [C_837,A_838,B_839] :
      ( v4_relat_1(C_837,A_838)
      | ~ m1_subset_1(C_837,k1_zfmisc_1(k2_zfmisc_1(A_838,B_839))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_13290,plain,(
    ! [C_843,A_844] :
      ( v4_relat_1(C_843,A_844)
      | ~ m1_subset_1(C_843,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_13261])).

tff(c_13296,plain,(
    ! [A_844] : v4_relat_1(k1_xboole_0,A_844) ),
    inference(resolution,[status(thm)],[c_236,c_13290])).

tff(c_232,plain,(
    ! [A_60] :
      ( k1_xboole_0 != A_60
      | k6_relat_1(A_60) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_228])).

tff(c_209,plain,(
    ! [A_37] : v1_relat_1(k6_relat_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_197])).

tff(c_42,plain,(
    ! [A_24] : k1_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_13394,plain,(
    ! [B_865,A_866] :
      ( r1_tarski(k1_relat_1(B_865),A_866)
      | ~ v4_relat_1(B_865,A_866)
      | ~ v1_relat_1(B_865) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_13416,plain,(
    ! [A_24,A_866] :
      ( r1_tarski(A_24,A_866)
      | ~ v4_relat_1(k6_relat_1(A_24),A_866)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_13394])).

tff(c_13425,plain,(
    ! [A_867,A_868] :
      ( r1_tarski(A_867,A_868)
      | ~ v4_relat_1(k6_relat_1(A_867),A_868) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_13416])).

tff(c_13449,plain,(
    ! [A_60,A_868] :
      ( r1_tarski(A_60,A_868)
      | ~ v4_relat_1(k1_xboole_0,A_868)
      | k1_xboole_0 != A_60 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_13425])).

tff(c_13463,plain,(
    ! [A_869,A_870] :
      ( r1_tarski(A_869,A_870)
      | k1_xboole_0 != A_869 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13296,c_13449])).

tff(c_336,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_350,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_74,c_336])).

tff(c_13186,plain,(
    ~ r1_tarski('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_13493,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_13463,c_13186])).

tff(c_18295,plain,(
    ! [A_1113] :
      ( r1_tarski('#skF_6',k2_zfmisc_1(A_1113,'#skF_5'))
      | ~ r1_tarski('#skF_3',A_1113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_14111,c_18278])).

tff(c_13973,plain,(
    ! [B_926,C_927,A_928] :
      ( k1_xboole_0 = B_926
      | v1_funct_2(C_927,A_928,B_926)
      | k1_relset_1(A_928,B_926,C_927) != A_928
      | ~ m1_subset_1(C_927,k1_zfmisc_1(k2_zfmisc_1(A_928,B_926))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_18757,plain,(
    ! [B_1134,A_1135,A_1136] :
      ( k1_xboole_0 = B_1134
      | v1_funct_2(A_1135,A_1136,B_1134)
      | k1_relset_1(A_1136,B_1134,A_1135) != A_1136
      | ~ r1_tarski(A_1135,k2_zfmisc_1(A_1136,B_1134)) ) ),
    inference(resolution,[status(thm)],[c_28,c_13973])).

tff(c_18760,plain,(
    ! [A_1113] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6',A_1113,'#skF_5')
      | k1_relset_1(A_1113,'#skF_5','#skF_6') != A_1113
      | ~ r1_tarski('#skF_3',A_1113) ) ),
    inference(resolution,[status(thm)],[c_18295,c_18757])).

tff(c_20293,plain,(
    ! [A_1166] :
      ( v1_funct_2('#skF_6',A_1166,'#skF_5')
      | k1_relset_1(A_1166,'#skF_5','#skF_6') != A_1166
      | ~ r1_tarski('#skF_3',A_1166) ) ),
    inference(negUnitSimplification,[status(thm)],[c_13493,c_18760])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_70,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_82,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_70])).

tff(c_162,plain,(
    ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_20301,plain,
    ( k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_20293,c_162])).

tff(c_20310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18626,c_20301])).

tff(c_20311,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_20752,plain,(
    ! [A_1233,B_1234,C_1235] :
      ( k2_relset_1(A_1233,B_1234,C_1235) = k2_relat_1(C_1235)
      | ~ m1_subset_1(C_1235,k1_zfmisc_1(k2_zfmisc_1(A_1233,B_1234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20765,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_20752])).

tff(c_20778,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20311,c_20765])).

tff(c_221,plain,
    ( k2_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_213,c_38])).

tff(c_270,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_20779,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20778,c_270])).

tff(c_20655,plain,(
    ! [A_1222,B_1223,C_1224] :
      ( k1_relset_1(A_1222,B_1223,C_1224) = k1_relat_1(C_1224)
      | ~ m1_subset_1(C_1224,k1_zfmisc_1(k2_zfmisc_1(A_1222,B_1223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20680,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_20655])).

tff(c_21108,plain,(
    ! [B_1282,A_1283,C_1284] :
      ( k1_xboole_0 = B_1282
      | k1_relset_1(A_1283,B_1282,C_1284) = A_1283
      | ~ v1_funct_2(C_1284,A_1283,B_1282)
      | ~ m1_subset_1(C_1284,k1_zfmisc_1(k2_zfmisc_1(A_1283,B_1282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_21124,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_21108])).

tff(c_21138,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_20680,c_21124])).

tff(c_21139,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_21138])).

tff(c_20880,plain,(
    ! [C_1248,A_1249,B_1250] :
      ( m1_subset_1(C_1248,k1_zfmisc_1(k2_zfmisc_1(A_1249,B_1250)))
      | ~ r1_tarski(k2_relat_1(C_1248),B_1250)
      | ~ r1_tarski(k1_relat_1(C_1248),A_1249)
      | ~ v1_relat_1(C_1248) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_50,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_relset_1(A_28,B_29,C_30) = k1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_25432,plain,(
    ! [A_1512,B_1513,C_1514] :
      ( k1_relset_1(A_1512,B_1513,C_1514) = k1_relat_1(C_1514)
      | ~ r1_tarski(k2_relat_1(C_1514),B_1513)
      | ~ r1_tarski(k1_relat_1(C_1514),A_1512)
      | ~ v1_relat_1(C_1514) ) ),
    inference(resolution,[status(thm)],[c_20880,c_50])).

tff(c_25438,plain,(
    ! [A_1512,B_1513] :
      ( k1_relset_1(A_1512,B_1513,'#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_5',B_1513)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_1512)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20778,c_25432])).

tff(c_25768,plain,(
    ! [A_1518,B_1519] :
      ( k1_relset_1(A_1518,B_1519,'#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_5',B_1519)
      | ~ r1_tarski('#skF_3',A_1518) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_21139,c_21139,c_25438])).

tff(c_26633,plain,(
    ! [A_1535] :
      ( k1_relset_1(A_1535,'#skF_5','#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_1535) ) ),
    inference(resolution,[status(thm)],[c_18,c_25768])).

tff(c_26653,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_26633])).

tff(c_54,plain,(
    ! [C_36,A_34,B_35] :
      ( m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ r1_tarski(k2_relat_1(C_36),B_35)
      | ~ r1_tarski(k1_relat_1(C_36),A_34)
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_21004,plain,(
    ! [B_1270,C_1271,A_1272] :
      ( k1_xboole_0 = B_1270
      | v1_funct_2(C_1271,A_1272,B_1270)
      | k1_relset_1(A_1272,B_1270,C_1271) != A_1272
      | ~ m1_subset_1(C_1271,k1_zfmisc_1(k2_zfmisc_1(A_1272,B_1270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_27482,plain,(
    ! [B_1551,C_1552,A_1553] :
      ( k1_xboole_0 = B_1551
      | v1_funct_2(C_1552,A_1553,B_1551)
      | k1_relset_1(A_1553,B_1551,C_1552) != A_1553
      | ~ r1_tarski(k2_relat_1(C_1552),B_1551)
      | ~ r1_tarski(k1_relat_1(C_1552),A_1553)
      | ~ v1_relat_1(C_1552) ) ),
    inference(resolution,[status(thm)],[c_54,c_21004])).

tff(c_27492,plain,(
    ! [B_1551,A_1553] :
      ( k1_xboole_0 = B_1551
      | v1_funct_2('#skF_6',A_1553,B_1551)
      | k1_relset_1(A_1553,B_1551,'#skF_6') != A_1553
      | ~ r1_tarski('#skF_5',B_1551)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_1553)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20778,c_27482])).

tff(c_27778,plain,(
    ! [B_1559,A_1560] :
      ( k1_xboole_0 = B_1559
      | v1_funct_2('#skF_6',A_1560,B_1559)
      | k1_relset_1(A_1560,B_1559,'#skF_6') != A_1560
      | ~ r1_tarski('#skF_5',B_1559)
      | ~ r1_tarski('#skF_3',A_1560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_21139,c_27492])).

tff(c_27789,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_27778,c_162])).

tff(c_27798,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_26653,c_27789])).

tff(c_27800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20779,c_27798])).

tff(c_27801,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_27810,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27801,c_98])).

tff(c_238,plain,(
    ! [A_61] :
      ( k1_xboole_0 != A_61
      | k6_relat_1(A_61) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_228])).

tff(c_249,plain,(
    ! [A_61] :
      ( k1_relat_1(k1_xboole_0) = A_61
      | k1_xboole_0 != A_61 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_42])).

tff(c_27919,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27801,c_27801,c_249])).

tff(c_28253,plain,(
    ! [A_1619,B_1620,C_1621] :
      ( k1_relset_1(A_1619,B_1620,C_1621) = k1_relat_1(C_1621)
      | ~ m1_subset_1(C_1621,k1_zfmisc_1(k2_zfmisc_1(A_1619,B_1620))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28269,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_28253])).

tff(c_28274,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27919,c_28269])).

tff(c_68,plain,(
    ! [B_39,A_38,C_40] :
      ( k1_xboole_0 = B_39
      | k1_relset_1(A_38,B_39,C_40) = A_38
      | ~ v1_funct_2(C_40,A_38,B_39)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_28831,plain,(
    ! [B_1685,A_1686,C_1687] :
      ( B_1685 = '#skF_6'
      | k1_relset_1(A_1686,B_1685,C_1687) = A_1686
      | ~ v1_funct_2(C_1687,A_1686,B_1685)
      | ~ m1_subset_1(C_1687,k1_zfmisc_1(k2_zfmisc_1(A_1686,B_1685))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27801,c_68])).

tff(c_28850,plain,
    ( '#skF_6' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_28831])).

tff(c_28858,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_28274,c_28850])).

tff(c_28859,plain,(
    '#skF_6' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_27810,c_28858])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_27811,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27801,c_12])).

tff(c_28906,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28859,c_27811])).

tff(c_27807,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_6',B_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27801,c_27801,c_24])).

tff(c_28904,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_3',B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28859,c_28859,c_27807])).

tff(c_27928,plain,(
    ! [A_1569,B_1570] :
      ( r2_hidden('#skF_2'(A_1569,B_1570),A_1569)
      | r1_tarski(A_1569,B_1570) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27932,plain,(
    ! [A_1569,B_1570] :
      ( ~ v1_xboole_0(A_1569)
      | r1_tarski(A_1569,B_1570) ) ),
    inference(resolution,[status(thm)],[c_27928,c_2])).

tff(c_174,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_190,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76,c_174])).

tff(c_27882,plain,(
    ! [B_1565,A_1566] :
      ( B_1565 = A_1566
      | ~ r1_tarski(B_1565,A_1566)
      | ~ r1_tarski(A_1566,B_1565) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_27889,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_190,c_27882])).

tff(c_28007,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_27889])).

tff(c_28011,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_27932,c_28007])).

tff(c_29017,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28904,c_28011])).

tff(c_29020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28906,c_29017])).

tff(c_29021,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_27889])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_27836,plain,(
    ! [B_13,A_12] :
      ( B_13 = '#skF_6'
      | A_12 = '#skF_6'
      | k2_zfmisc_1(A_12,B_13) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27801,c_27801,c_27801,c_20])).

tff(c_29030,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_29021,c_27836])).

tff(c_29037,plain,(
    '#skF_6' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_27810,c_29030])).

tff(c_27918,plain,(
    ! [A_61] :
      ( k1_relat_1('#skF_6') = A_61
      | A_61 != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27801,c_27801,c_249])).

tff(c_29210,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29037,c_29037,c_27918])).

tff(c_27804,plain,(
    ! [A_60] :
      ( A_60 != '#skF_6'
      | k6_relat_1(A_60) = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27801,c_27801,c_232])).

tff(c_29043,plain,(
    ! [A_60] :
      ( A_60 != '#skF_3'
      | k6_relat_1(A_60) = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29037,c_29037,c_27804])).

tff(c_27809,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27801,c_27801,c_22])).

tff(c_29045,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29037,c_29037,c_27809])).

tff(c_29219,plain,(
    ! [C_1707,A_1708,B_1709] :
      ( v4_relat_1(C_1707,A_1708)
      | ~ m1_subset_1(C_1707,k1_zfmisc_1(k2_zfmisc_1(A_1708,B_1709))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_29468,plain,(
    ! [C_1738,A_1739] :
      ( v4_relat_1(C_1738,A_1739)
      | ~ m1_subset_1(C_1738,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29045,c_29219])).

tff(c_29478,plain,(
    ! [A_1741,A_1742] :
      ( v4_relat_1(A_1741,A_1742)
      | ~ r1_tarski(A_1741,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_29468])).

tff(c_29270,plain,(
    ! [B_1716,A_1717] :
      ( r1_tarski(k1_relat_1(B_1716),A_1717)
      | ~ v4_relat_1(B_1716,A_1717)
      | ~ v1_relat_1(B_1716) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_29281,plain,(
    ! [A_24,A_1717] :
      ( r1_tarski(A_24,A_1717)
      | ~ v4_relat_1(k6_relat_1(A_24),A_1717)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_29270])).

tff(c_29286,plain,(
    ! [A_24,A_1717] :
      ( r1_tarski(A_24,A_1717)
      | ~ v4_relat_1(k6_relat_1(A_24),A_1717) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_29281])).

tff(c_29685,plain,(
    ! [A_1767,A_1768] :
      ( r1_tarski(A_1767,A_1768)
      | ~ r1_tarski(k6_relat_1(A_1767),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_29478,c_29286])).

tff(c_29693,plain,(
    ! [A_60,A_1768] :
      ( r1_tarski(A_60,A_1768)
      | ~ r1_tarski('#skF_3','#skF_3')
      | A_60 != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29043,c_29685])).

tff(c_29700,plain,(
    ! [A_60,A_1768] :
      ( r1_tarski(A_60,A_1768)
      | A_60 != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_29693])).

tff(c_29439,plain,(
    ! [A_1734,B_1735,C_1736] :
      ( k1_relset_1(A_1734,B_1735,C_1736) = k1_relat_1(C_1736)
      | ~ m1_subset_1(C_1736,k1_zfmisc_1(k2_zfmisc_1(A_1734,B_1735))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30437,plain,(
    ! [A_1851,B_1852,A_1853] :
      ( k1_relset_1(A_1851,B_1852,A_1853) = k1_relat_1(A_1853)
      | ~ r1_tarski(A_1853,k2_zfmisc_1(A_1851,B_1852)) ) ),
    inference(resolution,[status(thm)],[c_28,c_29439])).

tff(c_30481,plain,(
    ! [A_1851,B_1852] : k1_relset_1(A_1851,B_1852,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_29700,c_30437])).

tff(c_27803,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27801,c_27801,c_236])).

tff(c_29044,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29037,c_29037,c_27803])).

tff(c_29051,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29037,c_27801])).

tff(c_62,plain,(
    ! [C_40,B_39] :
      ( v1_funct_2(C_40,k1_xboole_0,B_39)
      | k1_relset_1(k1_xboole_0,B_39,C_40) != k1_xboole_0
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_84,plain,(
    ! [C_40,B_39] :
      ( v1_funct_2(C_40,k1_xboole_0,B_39)
      | k1_relset_1(k1_xboole_0,B_39,C_40) != k1_xboole_0
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_62])).

tff(c_29677,plain,(
    ! [C_1765,B_1766] :
      ( v1_funct_2(C_1765,'#skF_3',B_1766)
      | k1_relset_1('#skF_3',B_1766,C_1765) != '#skF_3'
      | ~ m1_subset_1(C_1765,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29051,c_29051,c_29051,c_29051,c_84])).

tff(c_29683,plain,(
    ! [B_1766] :
      ( v1_funct_2('#skF_3','#skF_3',B_1766)
      | k1_relset_1('#skF_3',B_1766,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_29044,c_29677])).

tff(c_30559,plain,(
    ! [B_1766] : v1_funct_2('#skF_3','#skF_3',B_1766) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29210,c_30481,c_29683])).

tff(c_29053,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29037,c_162])).

tff(c_30563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30559,c_29053])).

tff(c_30564,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_31671,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_31650,c_30564])).

tff(c_31688,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30727,c_31103,c_31671])).

tff(c_31697,plain,
    ( ~ v4_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_31688])).

tff(c_31706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30727,c_30965,c_31697])).

tff(c_31708,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_31728,plain,(
    ! [A_1984] : k2_zfmisc_1(A_1984,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31708,c_31708,c_22])).

tff(c_31732,plain,(
    v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_31728,c_36])).

tff(c_32082,plain,(
    ! [B_2019,A_2020] :
      ( v1_relat_1(B_2019)
      | ~ m1_subset_1(B_2019,k1_zfmisc_1(A_2020))
      | ~ v1_relat_1(A_2020) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32088,plain,(
    ! [A_37] :
      ( v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(k2_zfmisc_1(A_37,A_37)) ) ),
    inference(resolution,[status(thm)],[c_56,c_32082])).

tff(c_32099,plain,(
    ! [A_2021] : v1_relat_1(k6_relat_1(A_2021)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32088])).

tff(c_40,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_31824,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != '#skF_4'
      | A_23 = '#skF_4'
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31708,c_31708,c_40])).

tff(c_32102,plain,(
    ! [A_2021] :
      ( k1_relat_1(k6_relat_1(A_2021)) != '#skF_4'
      | k6_relat_1(A_2021) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_32099,c_31824])).

tff(c_32109,plain,(
    ! [A_2021] :
      ( A_2021 != '#skF_4'
      | k6_relat_1(A_2021) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32102])).

tff(c_31746,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31708,c_31708,c_24])).

tff(c_32342,plain,(
    ! [C_2049,A_2050,B_2051] :
      ( v4_relat_1(C_2049,A_2050)
      | ~ m1_subset_1(C_2049,k1_zfmisc_1(k2_zfmisc_1(A_2050,B_2051))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32359,plain,(
    ! [C_2052] :
      ( v4_relat_1(C_2052,'#skF_4')
      | ~ m1_subset_1(C_2052,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31746,c_32342])).

tff(c_32370,plain,(
    ! [A_2053] :
      ( v4_relat_1(A_2053,'#skF_4')
      | ~ r1_tarski(A_2053,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_32359])).

tff(c_32097,plain,(
    ! [A_37] : v1_relat_1(k6_relat_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32088])).

tff(c_32266,plain,(
    ! [B_2043,A_2044] :
      ( r1_tarski(k1_relat_1(B_2043),A_2044)
      | ~ v4_relat_1(B_2043,A_2044)
      | ~ v1_relat_1(B_2043) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32283,plain,(
    ! [A_24,A_2044] :
      ( r1_tarski(A_24,A_2044)
      | ~ v4_relat_1(k6_relat_1(A_24),A_2044)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_32266])).

tff(c_32291,plain,(
    ! [A_24,A_2044] :
      ( r1_tarski(A_24,A_2044)
      | ~ v4_relat_1(k6_relat_1(A_24),A_2044) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32097,c_32283])).

tff(c_32482,plain,(
    ! [A_2075] :
      ( r1_tarski(A_2075,'#skF_4')
      | ~ r1_tarski(k6_relat_1(A_2075),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32370,c_32291])).

tff(c_32488,plain,(
    ! [A_2021] :
      ( r1_tarski(A_2021,'#skF_4')
      | ~ r1_tarski('#skF_4','#skF_4')
      | A_2021 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32109,c_32482])).

tff(c_32493,plain,(
    ! [A_2076] :
      ( r1_tarski(A_2076,'#skF_4')
      | A_2076 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32488])).

tff(c_32098,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(A_14)
      | ~ v1_relat_1(B_15)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(resolution,[status(thm)],[c_28,c_32082])).

tff(c_32509,plain,(
    ! [A_2076] :
      ( v1_relat_1(A_2076)
      | ~ v1_relat_1('#skF_4')
      | A_2076 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_32493,c_32098])).

tff(c_32520,plain,(
    ! [A_2076] :
      ( v1_relat_1(A_2076)
      | A_2076 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31732,c_32509])).

tff(c_31727,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31708,c_31708,c_22])).

tff(c_32383,plain,(
    ! [C_2054,A_2055] :
      ( v4_relat_1(C_2054,A_2055)
      | ~ m1_subset_1(C_2054,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31727,c_32342])).

tff(c_32462,plain,(
    ! [A_2067,A_2068] :
      ( v4_relat_1(A_2067,A_2068)
      | ~ r1_tarski(A_2067,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_32383])).

tff(c_32682,plain,(
    ! [A_2091,A_2092] :
      ( r1_tarski(A_2091,A_2092)
      | ~ r1_tarski(k6_relat_1(A_2091),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32462,c_32291])).

tff(c_32693,plain,(
    ! [A_2021,A_2092] :
      ( r1_tarski(A_2021,A_2092)
      | ~ r1_tarski('#skF_4','#skF_4')
      | A_2021 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32109,c_32682])).

tff(c_32698,plain,(
    ! [A_2021,A_2092] :
      ( r1_tarski(A_2021,A_2092)
      | A_2021 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32693])).

tff(c_32975,plain,(
    ! [A_2135,A_2136,B_2137] :
      ( v4_relat_1(A_2135,A_2136)
      | ~ r1_tarski(A_2135,k2_zfmisc_1(A_2136,B_2137)) ) ),
    inference(resolution,[status(thm)],[c_28,c_32342])).

tff(c_33006,plain,(
    ! [A_2021,A_2136] :
      ( v4_relat_1(A_2021,A_2136)
      | A_2021 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_32698,c_32975])).

tff(c_31707,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_31714,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31708,c_31707])).

tff(c_31709,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31707,c_12])).

tff(c_31725,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31714,c_31709])).

tff(c_31939,plain,(
    ! [A_2004,B_2005] :
      ( r2_hidden('#skF_2'(A_2004,B_2005),A_2004)
      | r1_tarski(A_2004,B_2005) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_31944,plain,(
    ! [A_2006,B_2007] :
      ( ~ v1_xboole_0(A_2006)
      | r1_tarski(A_2006,B_2007) ) ),
    inference(resolution,[status(thm)],[c_31939,c_2])).

tff(c_31766,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31727,c_31714,c_76])).

tff(c_31773,plain,(
    ! [A_1992,B_1993] :
      ( r1_tarski(A_1992,B_1993)
      | ~ m1_subset_1(A_1992,k1_zfmisc_1(B_1993)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_31781,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_31766,c_31773])).

tff(c_31835,plain,(
    ! [B_1998,A_1999] :
      ( B_1998 = A_1999
      | ~ r1_tarski(B_1998,A_1999)
      | ~ r1_tarski(A_1999,B_1998) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_31848,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_31781,c_31835])).

tff(c_31854,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_31848])).

tff(c_31947,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_31944,c_31854])).

tff(c_31953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31725,c_31947])).

tff(c_31954,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_31848])).

tff(c_31959,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31954,c_31766])).

tff(c_32389,plain,(
    ! [A_2055] : v4_relat_1('#skF_4',A_2055) ),
    inference(resolution,[status(thm)],[c_31959,c_32383])).

tff(c_31990,plain,(
    ! [B_2012,A_2013] :
      ( v1_relat_1(B_2012)
      | ~ m1_subset_1(B_2012,k1_zfmisc_1(A_2013))
      | ~ v1_relat_1(A_2013) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_31999,plain,(
    ! [A_37] :
      ( v1_relat_1(k6_relat_1(A_37))
      | ~ v1_relat_1(k2_zfmisc_1(A_37,A_37)) ) ),
    inference(resolution,[status(thm)],[c_56,c_31990])).

tff(c_32015,plain,(
    ! [A_2014] : v1_relat_1(k6_relat_1(A_2014)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_31999])).

tff(c_32018,plain,(
    ! [A_2014] :
      ( k1_relat_1(k6_relat_1(A_2014)) != '#skF_4'
      | k6_relat_1(A_2014) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_32015,c_31824])).

tff(c_32027,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32018])).

tff(c_31793,plain,(
    ! [A_1995] : m1_subset_1(k6_relat_1(A_1995),k1_zfmisc_1(k2_zfmisc_1(A_1995,A_1995))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_31800,plain,(
    m1_subset_1(k6_relat_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_31746,c_31793])).

tff(c_31809,plain,(
    r1_tarski(k6_relat_1('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_31800,c_26])).

tff(c_31847,plain,
    ( k6_relat_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k6_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_31809,c_31835])).

tff(c_31976,plain,(
    ~ r1_tarski('#skF_4',k6_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_31847])).

tff(c_32028,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32027,c_31976])).

tff(c_32033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_32028])).

tff(c_32034,plain,(
    k6_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_31847])).

tff(c_32049,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_32034,c_42])).

tff(c_32280,plain,(
    ! [A_2044] :
      ( r1_tarski('#skF_4',A_2044)
      | ~ v4_relat_1('#skF_4',A_2044)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32049,c_32266])).

tff(c_32289,plain,(
    ! [A_2044] :
      ( r1_tarski('#skF_4',A_2044)
      | ~ v4_relat_1('#skF_4',A_2044) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31732,c_32280])).

tff(c_32397,plain,(
    ! [A_2057] : r1_tarski('#skF_4',A_2057) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32389,c_32289])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32432,plain,(
    ! [A_2063] :
      ( A_2063 = '#skF_4'
      | ~ r1_tarski(A_2063,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32397,c_14])).

tff(c_33415,plain,(
    ! [B_2173] :
      ( k1_relat_1(B_2173) = '#skF_4'
      | ~ v4_relat_1(B_2173,'#skF_4')
      | ~ v1_relat_1(B_2173) ) ),
    inference(resolution,[status(thm)],[c_34,c_32432])).

tff(c_33470,plain,(
    ! [A_2174] :
      ( k1_relat_1(A_2174) = '#skF_4'
      | ~ v1_relat_1(A_2174)
      | A_2174 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_33006,c_33415])).

tff(c_33488,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32520,c_33470])).

tff(c_32598,plain,(
    ! [A_2082,B_2083,C_2084] :
      ( k1_relset_1(A_2082,B_2083,C_2084) = k1_relat_1(C_2084)
      | ~ m1_subset_1(C_2084,k1_zfmisc_1(k2_zfmisc_1(A_2082,B_2083))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34075,plain,(
    ! [B_2213,C_2214] :
      ( k1_relset_1('#skF_4',B_2213,C_2214) = k1_relat_1(C_2214)
      | ~ m1_subset_1(C_2214,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31746,c_32598])).

tff(c_34077,plain,(
    ! [B_2213] : k1_relset_1('#skF_4',B_2213,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_31959,c_34075])).

tff(c_34082,plain,(
    ! [B_2213] : k1_relset_1('#skF_4',B_2213,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33488,c_34077])).

tff(c_32963,plain,(
    ! [C_2129,B_2130] :
      ( v1_funct_2(C_2129,'#skF_4',B_2130)
      | k1_relset_1('#skF_4',B_2130,C_2129) != '#skF_4'
      | ~ m1_subset_1(C_2129,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31708,c_31708,c_31708,c_31708,c_84])).

tff(c_33012,plain,(
    ! [B_2138] :
      ( v1_funct_2('#skF_4','#skF_4',B_2138)
      | k1_relset_1('#skF_4',B_2138,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_31959,c_32963])).

tff(c_31811,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31714,c_31766,c_31746,c_31714,c_82])).

tff(c_31956,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31954,c_31811])).

tff(c_33028,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_33012,c_31956])).

tff(c_34088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34082,c_33028])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.70/5.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/5.36  
% 13.75/5.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/5.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 13.75/5.37  
% 13.75/5.37  %Foreground sorts:
% 13.75/5.37  
% 13.75/5.37  
% 13.75/5.37  %Background operators:
% 13.75/5.37  
% 13.75/5.37  
% 13.75/5.37  %Foreground operators:
% 13.75/5.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.75/5.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.75/5.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.75/5.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.75/5.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.75/5.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.75/5.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.75/5.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.75/5.37  tff('#skF_5', type, '#skF_5': $i).
% 13.75/5.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.75/5.37  tff('#skF_6', type, '#skF_6': $i).
% 13.75/5.37  tff('#skF_3', type, '#skF_3': $i).
% 13.75/5.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.75/5.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.75/5.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.75/5.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.75/5.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.75/5.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.75/5.37  tff('#skF_4', type, '#skF_4': $i).
% 13.75/5.37  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.75/5.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.75/5.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.75/5.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.75/5.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.75/5.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.75/5.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.75/5.37  
% 13.75/5.41  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.75/5.41  tff(f_144, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 13.75/5.41  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.75/5.41  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.75/5.41  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 13.75/5.41  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.75/5.41  tff(f_104, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 13.75/5.41  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.75/5.41  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.75/5.41  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 13.75/5.41  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.75/5.41  tff(f_82, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 13.75/5.41  tff(f_106, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 13.75/5.41  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 13.75/5.41  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.75/5.41  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.75/5.41  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 13.75/5.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.75/5.41  tff(c_36, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.75/5.41  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.75/5.41  tff(c_30705, plain, (![B_1876, A_1877]: (v1_relat_1(B_1876) | ~m1_subset_1(B_1876, k1_zfmisc_1(A_1877)) | ~v1_relat_1(A_1877))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.75/5.41  tff(c_30717, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_30705])).
% 13.75/5.41  tff(c_30727, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30717])).
% 13.75/5.41  tff(c_30942, plain, (![C_1897, A_1898, B_1899]: (v4_relat_1(C_1897, A_1898) | ~m1_subset_1(C_1897, k1_zfmisc_1(k2_zfmisc_1(A_1898, B_1899))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.75/5.41  tff(c_30965, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_76, c_30942])).
% 13.75/5.41  tff(c_34, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.75/5.41  tff(c_31064, plain, (![A_1912, B_1913, C_1914]: (k2_relset_1(A_1912, B_1913, C_1914)=k2_relat_1(C_1914) | ~m1_subset_1(C_1914, k1_zfmisc_1(k2_zfmisc_1(A_1912, B_1913))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.75/5.41  tff(c_31089, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_31064])).
% 13.75/5.41  tff(c_74, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.75/5.41  tff(c_31103, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31089, c_74])).
% 13.75/5.41  tff(c_31650, plain, (![C_1979, A_1980, B_1981]: (m1_subset_1(C_1979, k1_zfmisc_1(k2_zfmisc_1(A_1980, B_1981))) | ~r1_tarski(k2_relat_1(C_1979), B_1981) | ~r1_tarski(k1_relat_1(C_1979), A_1980) | ~v1_relat_1(C_1979))), inference(cnfTransformation, [status(thm)], [f_104])).
% 13.75/5.41  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.75/5.41  tff(c_72, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.75/5.41  tff(c_98, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_72])).
% 13.75/5.41  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.75/5.41  tff(c_13755, plain, (![A_900, B_901, C_902]: (k1_relset_1(A_900, B_901, C_902)=k1_relat_1(C_902) | ~m1_subset_1(C_902, k1_zfmisc_1(k2_zfmisc_1(A_900, B_901))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.75/5.41  tff(c_13780, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_13755])).
% 13.75/5.41  tff(c_14080, plain, (![B_938, A_939, C_940]: (k1_xboole_0=B_938 | k1_relset_1(A_939, B_938, C_940)=A_939 | ~v1_funct_2(C_940, A_939, B_938) | ~m1_subset_1(C_940, k1_zfmisc_1(k2_zfmisc_1(A_939, B_938))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.75/5.41  tff(c_14096, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_14080])).
% 13.75/5.41  tff(c_14110, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_13780, c_14096])).
% 13.75/5.41  tff(c_14111, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_98, c_14110])).
% 13.75/5.41  tff(c_191, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.75/5.41  tff(c_203, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_191])).
% 13.75/5.41  tff(c_213, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_203])).
% 13.75/5.41  tff(c_13647, plain, (![A_891, B_892, C_893]: (k2_relset_1(A_891, B_892, C_893)=k2_relat_1(C_893) | ~m1_subset_1(C_893, k1_zfmisc_1(k2_zfmisc_1(A_891, B_892))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.75/5.41  tff(c_13672, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_13647])).
% 13.75/5.41  tff(c_13689, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13672, c_74])).
% 13.75/5.41  tff(c_13863, plain, (![C_914, A_915, B_916]: (m1_subset_1(C_914, k1_zfmisc_1(k2_zfmisc_1(A_915, B_916))) | ~r1_tarski(k2_relat_1(C_914), B_916) | ~r1_tarski(k1_relat_1(C_914), A_915) | ~v1_relat_1(C_914))), inference(cnfTransformation, [status(thm)], [f_104])).
% 13.75/5.41  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.75/5.41  tff(c_18276, plain, (![C_1112, A_1113, B_1114]: (r1_tarski(C_1112, k2_zfmisc_1(A_1113, B_1114)) | ~r1_tarski(k2_relat_1(C_1112), B_1114) | ~r1_tarski(k1_relat_1(C_1112), A_1113) | ~v1_relat_1(C_1112))), inference(resolution, [status(thm)], [c_13863, c_26])).
% 13.75/5.41  tff(c_18278, plain, (![A_1113]: (r1_tarski('#skF_6', k2_zfmisc_1(A_1113, '#skF_5')) | ~r1_tarski(k1_relat_1('#skF_6'), A_1113) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_13689, c_18276])).
% 13.75/5.41  tff(c_18302, plain, (![A_1115]: (r1_tarski('#skF_6', k2_zfmisc_1(A_1115, '#skF_5')) | ~r1_tarski('#skF_3', A_1115))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_14111, c_18278])).
% 13.75/5.41  tff(c_28, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.75/5.41  tff(c_13779, plain, (![A_900, B_901, A_14]: (k1_relset_1(A_900, B_901, A_14)=k1_relat_1(A_14) | ~r1_tarski(A_14, k2_zfmisc_1(A_900, B_901)))), inference(resolution, [status(thm)], [c_28, c_13755])).
% 13.75/5.41  tff(c_18310, plain, (![A_1115]: (k1_relset_1(A_1115, '#skF_5', '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski('#skF_3', A_1115))), inference(resolution, [status(thm)], [c_18302, c_13779])).
% 13.75/5.41  tff(c_18606, plain, (![A_1125]: (k1_relset_1(A_1125, '#skF_5', '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_1125))), inference(demodulation, [status(thm), theory('equality')], [c_14111, c_18310])).
% 13.75/5.41  tff(c_18626, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_18, c_18606])).
% 13.75/5.41  tff(c_44, plain, (![A_24]: (k2_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.75/5.41  tff(c_56, plain, (![A_37]: (m1_subset_1(k6_relat_1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.75/5.41  tff(c_197, plain, (![A_37]: (v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(k2_zfmisc_1(A_37, A_37)))), inference(resolution, [status(thm)], [c_56, c_191])).
% 13.75/5.41  tff(c_222, plain, (![A_60]: (v1_relat_1(k6_relat_1(A_60)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_197])).
% 13.75/5.41  tff(c_38, plain, (![A_23]: (k2_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.75/5.41  tff(c_228, plain, (![A_60]: (k2_relat_1(k6_relat_1(A_60))!=k1_xboole_0 | k6_relat_1(A_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_222, c_38])).
% 13.75/5.41  tff(c_234, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_228])).
% 13.75/5.41  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.75/5.41  tff(c_153, plain, (![A_54]: (m1_subset_1(k6_relat_1(A_54), k1_zfmisc_1(k2_zfmisc_1(A_54, A_54))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.75/5.41  tff(c_157, plain, (m1_subset_1(k6_relat_1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_153])).
% 13.75/5.41  tff(c_236, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_234, c_157])).
% 13.75/5.41  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.75/5.41  tff(c_13261, plain, (![C_837, A_838, B_839]: (v4_relat_1(C_837, A_838) | ~m1_subset_1(C_837, k1_zfmisc_1(k2_zfmisc_1(A_838, B_839))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.75/5.41  tff(c_13290, plain, (![C_843, A_844]: (v4_relat_1(C_843, A_844) | ~m1_subset_1(C_843, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_13261])).
% 13.75/5.41  tff(c_13296, plain, (![A_844]: (v4_relat_1(k1_xboole_0, A_844))), inference(resolution, [status(thm)], [c_236, c_13290])).
% 13.75/5.41  tff(c_232, plain, (![A_60]: (k1_xboole_0!=A_60 | k6_relat_1(A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_228])).
% 13.75/5.41  tff(c_209, plain, (![A_37]: (v1_relat_1(k6_relat_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_197])).
% 13.75/5.41  tff(c_42, plain, (![A_24]: (k1_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.75/5.41  tff(c_13394, plain, (![B_865, A_866]: (r1_tarski(k1_relat_1(B_865), A_866) | ~v4_relat_1(B_865, A_866) | ~v1_relat_1(B_865))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.75/5.41  tff(c_13416, plain, (![A_24, A_866]: (r1_tarski(A_24, A_866) | ~v4_relat_1(k6_relat_1(A_24), A_866) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_13394])).
% 13.75/5.41  tff(c_13425, plain, (![A_867, A_868]: (r1_tarski(A_867, A_868) | ~v4_relat_1(k6_relat_1(A_867), A_868))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_13416])).
% 13.75/5.41  tff(c_13449, plain, (![A_60, A_868]: (r1_tarski(A_60, A_868) | ~v4_relat_1(k1_xboole_0, A_868) | k1_xboole_0!=A_60)), inference(superposition, [status(thm), theory('equality')], [c_232, c_13425])).
% 13.75/5.41  tff(c_13463, plain, (![A_869, A_870]: (r1_tarski(A_869, A_870) | k1_xboole_0!=A_869)), inference(demodulation, [status(thm), theory('equality')], [c_13296, c_13449])).
% 13.75/5.41  tff(c_336, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.75/5.41  tff(c_350, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_5' | ~r1_tarski('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_336])).
% 13.75/5.41  tff(c_13186, plain, (~r1_tarski('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_350])).
% 13.75/5.41  tff(c_13493, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_13463, c_13186])).
% 13.75/5.41  tff(c_18295, plain, (![A_1113]: (r1_tarski('#skF_6', k2_zfmisc_1(A_1113, '#skF_5')) | ~r1_tarski('#skF_3', A_1113))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_14111, c_18278])).
% 13.75/5.41  tff(c_13973, plain, (![B_926, C_927, A_928]: (k1_xboole_0=B_926 | v1_funct_2(C_927, A_928, B_926) | k1_relset_1(A_928, B_926, C_927)!=A_928 | ~m1_subset_1(C_927, k1_zfmisc_1(k2_zfmisc_1(A_928, B_926))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.75/5.41  tff(c_18757, plain, (![B_1134, A_1135, A_1136]: (k1_xboole_0=B_1134 | v1_funct_2(A_1135, A_1136, B_1134) | k1_relset_1(A_1136, B_1134, A_1135)!=A_1136 | ~r1_tarski(A_1135, k2_zfmisc_1(A_1136, B_1134)))), inference(resolution, [status(thm)], [c_28, c_13973])).
% 13.75/5.41  tff(c_18760, plain, (![A_1113]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', A_1113, '#skF_5') | k1_relset_1(A_1113, '#skF_5', '#skF_6')!=A_1113 | ~r1_tarski('#skF_3', A_1113))), inference(resolution, [status(thm)], [c_18295, c_18757])).
% 13.75/5.41  tff(c_20293, plain, (![A_1166]: (v1_funct_2('#skF_6', A_1166, '#skF_5') | k1_relset_1(A_1166, '#skF_5', '#skF_6')!=A_1166 | ~r1_tarski('#skF_3', A_1166))), inference(negUnitSimplification, [status(thm)], [c_13493, c_18760])).
% 13.75/5.41  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.75/5.41  tff(c_70, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.75/5.41  tff(c_82, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_70])).
% 13.75/5.41  tff(c_162, plain, (~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_82])).
% 13.75/5.41  tff(c_20301, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_20293, c_162])).
% 13.75/5.41  tff(c_20310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_18626, c_20301])).
% 13.75/5.41  tff(c_20311, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_350])).
% 13.75/5.41  tff(c_20752, plain, (![A_1233, B_1234, C_1235]: (k2_relset_1(A_1233, B_1234, C_1235)=k2_relat_1(C_1235) | ~m1_subset_1(C_1235, k1_zfmisc_1(k2_zfmisc_1(A_1233, B_1234))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.75/5.41  tff(c_20765, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_20752])).
% 13.75/5.41  tff(c_20778, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20311, c_20765])).
% 13.75/5.41  tff(c_221, plain, (k2_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_213, c_38])).
% 13.75/5.41  tff(c_270, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_221])).
% 13.75/5.41  tff(c_20779, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20778, c_270])).
% 13.75/5.41  tff(c_20655, plain, (![A_1222, B_1223, C_1224]: (k1_relset_1(A_1222, B_1223, C_1224)=k1_relat_1(C_1224) | ~m1_subset_1(C_1224, k1_zfmisc_1(k2_zfmisc_1(A_1222, B_1223))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.75/5.41  tff(c_20680, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_20655])).
% 13.75/5.41  tff(c_21108, plain, (![B_1282, A_1283, C_1284]: (k1_xboole_0=B_1282 | k1_relset_1(A_1283, B_1282, C_1284)=A_1283 | ~v1_funct_2(C_1284, A_1283, B_1282) | ~m1_subset_1(C_1284, k1_zfmisc_1(k2_zfmisc_1(A_1283, B_1282))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.75/5.41  tff(c_21124, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_21108])).
% 13.75/5.41  tff(c_21138, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_20680, c_21124])).
% 13.75/5.41  tff(c_21139, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_98, c_21138])).
% 13.75/5.41  tff(c_20880, plain, (![C_1248, A_1249, B_1250]: (m1_subset_1(C_1248, k1_zfmisc_1(k2_zfmisc_1(A_1249, B_1250))) | ~r1_tarski(k2_relat_1(C_1248), B_1250) | ~r1_tarski(k1_relat_1(C_1248), A_1249) | ~v1_relat_1(C_1248))), inference(cnfTransformation, [status(thm)], [f_104])).
% 13.75/5.41  tff(c_50, plain, (![A_28, B_29, C_30]: (k1_relset_1(A_28, B_29, C_30)=k1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.75/5.41  tff(c_25432, plain, (![A_1512, B_1513, C_1514]: (k1_relset_1(A_1512, B_1513, C_1514)=k1_relat_1(C_1514) | ~r1_tarski(k2_relat_1(C_1514), B_1513) | ~r1_tarski(k1_relat_1(C_1514), A_1512) | ~v1_relat_1(C_1514))), inference(resolution, [status(thm)], [c_20880, c_50])).
% 13.75/5.41  tff(c_25438, plain, (![A_1512, B_1513]: (k1_relset_1(A_1512, B_1513, '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski('#skF_5', B_1513) | ~r1_tarski(k1_relat_1('#skF_6'), A_1512) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20778, c_25432])).
% 13.75/5.41  tff(c_25768, plain, (![A_1518, B_1519]: (k1_relset_1(A_1518, B_1519, '#skF_6')='#skF_3' | ~r1_tarski('#skF_5', B_1519) | ~r1_tarski('#skF_3', A_1518))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_21139, c_21139, c_25438])).
% 13.75/5.41  tff(c_26633, plain, (![A_1535]: (k1_relset_1(A_1535, '#skF_5', '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_1535))), inference(resolution, [status(thm)], [c_18, c_25768])).
% 13.75/5.41  tff(c_26653, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_18, c_26633])).
% 13.75/5.41  tff(c_54, plain, (![C_36, A_34, B_35]: (m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~r1_tarski(k2_relat_1(C_36), B_35) | ~r1_tarski(k1_relat_1(C_36), A_34) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_104])).
% 13.75/5.41  tff(c_21004, plain, (![B_1270, C_1271, A_1272]: (k1_xboole_0=B_1270 | v1_funct_2(C_1271, A_1272, B_1270) | k1_relset_1(A_1272, B_1270, C_1271)!=A_1272 | ~m1_subset_1(C_1271, k1_zfmisc_1(k2_zfmisc_1(A_1272, B_1270))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.75/5.41  tff(c_27482, plain, (![B_1551, C_1552, A_1553]: (k1_xboole_0=B_1551 | v1_funct_2(C_1552, A_1553, B_1551) | k1_relset_1(A_1553, B_1551, C_1552)!=A_1553 | ~r1_tarski(k2_relat_1(C_1552), B_1551) | ~r1_tarski(k1_relat_1(C_1552), A_1553) | ~v1_relat_1(C_1552))), inference(resolution, [status(thm)], [c_54, c_21004])).
% 13.75/5.41  tff(c_27492, plain, (![B_1551, A_1553]: (k1_xboole_0=B_1551 | v1_funct_2('#skF_6', A_1553, B_1551) | k1_relset_1(A_1553, B_1551, '#skF_6')!=A_1553 | ~r1_tarski('#skF_5', B_1551) | ~r1_tarski(k1_relat_1('#skF_6'), A_1553) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20778, c_27482])).
% 13.75/5.41  tff(c_27778, plain, (![B_1559, A_1560]: (k1_xboole_0=B_1559 | v1_funct_2('#skF_6', A_1560, B_1559) | k1_relset_1(A_1560, B_1559, '#skF_6')!=A_1560 | ~r1_tarski('#skF_5', B_1559) | ~r1_tarski('#skF_3', A_1560))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_21139, c_27492])).
% 13.75/5.41  tff(c_27789, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_5', '#skF_5') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_27778, c_162])).
% 13.75/5.41  tff(c_27798, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_26653, c_27789])).
% 13.75/5.41  tff(c_27800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20779, c_27798])).
% 13.75/5.41  tff(c_27801, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_221])).
% 13.75/5.41  tff(c_27810, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_27801, c_98])).
% 13.75/5.41  tff(c_238, plain, (![A_61]: (k1_xboole_0!=A_61 | k6_relat_1(A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_228])).
% 13.75/5.41  tff(c_249, plain, (![A_61]: (k1_relat_1(k1_xboole_0)=A_61 | k1_xboole_0!=A_61)), inference(superposition, [status(thm), theory('equality')], [c_238, c_42])).
% 13.75/5.41  tff(c_27919, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_27801, c_27801, c_249])).
% 13.75/5.41  tff(c_28253, plain, (![A_1619, B_1620, C_1621]: (k1_relset_1(A_1619, B_1620, C_1621)=k1_relat_1(C_1621) | ~m1_subset_1(C_1621, k1_zfmisc_1(k2_zfmisc_1(A_1619, B_1620))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.75/5.41  tff(c_28269, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_28253])).
% 13.75/5.41  tff(c_28274, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_27919, c_28269])).
% 13.75/5.41  tff(c_68, plain, (![B_39, A_38, C_40]: (k1_xboole_0=B_39 | k1_relset_1(A_38, B_39, C_40)=A_38 | ~v1_funct_2(C_40, A_38, B_39) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.75/5.41  tff(c_28831, plain, (![B_1685, A_1686, C_1687]: (B_1685='#skF_6' | k1_relset_1(A_1686, B_1685, C_1687)=A_1686 | ~v1_funct_2(C_1687, A_1686, B_1685) | ~m1_subset_1(C_1687, k1_zfmisc_1(k2_zfmisc_1(A_1686, B_1685))))), inference(demodulation, [status(thm), theory('equality')], [c_27801, c_68])).
% 13.75/5.41  tff(c_28850, plain, ('#skF_6'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_76, c_28831])).
% 13.75/5.41  tff(c_28858, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_28274, c_28850])).
% 13.75/5.41  tff(c_28859, plain, ('#skF_6'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_27810, c_28858])).
% 13.75/5.41  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.75/5.41  tff(c_27811, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27801, c_12])).
% 13.75/5.41  tff(c_28906, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28859, c_27811])).
% 13.75/5.41  tff(c_27807, plain, (![B_13]: (k2_zfmisc_1('#skF_6', B_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27801, c_27801, c_24])).
% 13.75/5.41  tff(c_28904, plain, (![B_13]: (k2_zfmisc_1('#skF_3', B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28859, c_28859, c_27807])).
% 13.75/5.41  tff(c_27928, plain, (![A_1569, B_1570]: (r2_hidden('#skF_2'(A_1569, B_1570), A_1569) | r1_tarski(A_1569, B_1570))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.75/5.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.75/5.41  tff(c_27932, plain, (![A_1569, B_1570]: (~v1_xboole_0(A_1569) | r1_tarski(A_1569, B_1570))), inference(resolution, [status(thm)], [c_27928, c_2])).
% 13.75/5.41  tff(c_174, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.75/5.41  tff(c_190, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76, c_174])).
% 13.75/5.41  tff(c_27882, plain, (![B_1565, A_1566]: (B_1565=A_1566 | ~r1_tarski(B_1565, A_1566) | ~r1_tarski(A_1566, B_1565))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.75/5.41  tff(c_27889, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(resolution, [status(thm)], [c_190, c_27882])).
% 13.75/5.41  tff(c_28007, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_27889])).
% 13.75/5.41  tff(c_28011, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_27932, c_28007])).
% 13.75/5.41  tff(c_29017, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28904, c_28011])).
% 13.75/5.41  tff(c_29020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28906, c_29017])).
% 13.75/5.41  tff(c_29021, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_27889])).
% 13.75/5.41  tff(c_20, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.75/5.41  tff(c_27836, plain, (![B_13, A_12]: (B_13='#skF_6' | A_12='#skF_6' | k2_zfmisc_1(A_12, B_13)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27801, c_27801, c_27801, c_20])).
% 13.75/5.41  tff(c_29030, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_29021, c_27836])).
% 13.75/5.41  tff(c_29037, plain, ('#skF_6'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_27810, c_29030])).
% 13.75/5.41  tff(c_27918, plain, (![A_61]: (k1_relat_1('#skF_6')=A_61 | A_61!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27801, c_27801, c_249])).
% 13.75/5.41  tff(c_29210, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_29037, c_29037, c_27918])).
% 13.75/5.41  tff(c_27804, plain, (![A_60]: (A_60!='#skF_6' | k6_relat_1(A_60)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27801, c_27801, c_232])).
% 13.75/5.41  tff(c_29043, plain, (![A_60]: (A_60!='#skF_3' | k6_relat_1(A_60)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_29037, c_29037, c_27804])).
% 13.75/5.41  tff(c_27809, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27801, c_27801, c_22])).
% 13.75/5.41  tff(c_29045, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_29037, c_29037, c_27809])).
% 13.75/5.41  tff(c_29219, plain, (![C_1707, A_1708, B_1709]: (v4_relat_1(C_1707, A_1708) | ~m1_subset_1(C_1707, k1_zfmisc_1(k2_zfmisc_1(A_1708, B_1709))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.75/5.41  tff(c_29468, plain, (![C_1738, A_1739]: (v4_relat_1(C_1738, A_1739) | ~m1_subset_1(C_1738, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_29045, c_29219])).
% 13.75/5.41  tff(c_29478, plain, (![A_1741, A_1742]: (v4_relat_1(A_1741, A_1742) | ~r1_tarski(A_1741, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_29468])).
% 13.75/5.41  tff(c_29270, plain, (![B_1716, A_1717]: (r1_tarski(k1_relat_1(B_1716), A_1717) | ~v4_relat_1(B_1716, A_1717) | ~v1_relat_1(B_1716))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.75/5.41  tff(c_29281, plain, (![A_24, A_1717]: (r1_tarski(A_24, A_1717) | ~v4_relat_1(k6_relat_1(A_24), A_1717) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_29270])).
% 13.75/5.41  tff(c_29286, plain, (![A_24, A_1717]: (r1_tarski(A_24, A_1717) | ~v4_relat_1(k6_relat_1(A_24), A_1717))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_29281])).
% 13.75/5.41  tff(c_29685, plain, (![A_1767, A_1768]: (r1_tarski(A_1767, A_1768) | ~r1_tarski(k6_relat_1(A_1767), '#skF_3'))), inference(resolution, [status(thm)], [c_29478, c_29286])).
% 13.75/5.41  tff(c_29693, plain, (![A_60, A_1768]: (r1_tarski(A_60, A_1768) | ~r1_tarski('#skF_3', '#skF_3') | A_60!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29043, c_29685])).
% 13.75/5.41  tff(c_29700, plain, (![A_60, A_1768]: (r1_tarski(A_60, A_1768) | A_60!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_29693])).
% 13.75/5.41  tff(c_29439, plain, (![A_1734, B_1735, C_1736]: (k1_relset_1(A_1734, B_1735, C_1736)=k1_relat_1(C_1736) | ~m1_subset_1(C_1736, k1_zfmisc_1(k2_zfmisc_1(A_1734, B_1735))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.75/5.41  tff(c_30437, plain, (![A_1851, B_1852, A_1853]: (k1_relset_1(A_1851, B_1852, A_1853)=k1_relat_1(A_1853) | ~r1_tarski(A_1853, k2_zfmisc_1(A_1851, B_1852)))), inference(resolution, [status(thm)], [c_28, c_29439])).
% 13.75/5.41  tff(c_30481, plain, (![A_1851, B_1852]: (k1_relset_1(A_1851, B_1852, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_29700, c_30437])).
% 13.75/5.41  tff(c_27803, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_27801, c_27801, c_236])).
% 13.75/5.41  tff(c_29044, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_29037, c_29037, c_27803])).
% 13.75/5.41  tff(c_29051, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_29037, c_27801])).
% 13.75/5.41  tff(c_62, plain, (![C_40, B_39]: (v1_funct_2(C_40, k1_xboole_0, B_39) | k1_relset_1(k1_xboole_0, B_39, C_40)!=k1_xboole_0 | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_39))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.75/5.41  tff(c_84, plain, (![C_40, B_39]: (v1_funct_2(C_40, k1_xboole_0, B_39) | k1_relset_1(k1_xboole_0, B_39, C_40)!=k1_xboole_0 | ~m1_subset_1(C_40, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_62])).
% 13.75/5.41  tff(c_29677, plain, (![C_1765, B_1766]: (v1_funct_2(C_1765, '#skF_3', B_1766) | k1_relset_1('#skF_3', B_1766, C_1765)!='#skF_3' | ~m1_subset_1(C_1765, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_29051, c_29051, c_29051, c_29051, c_84])).
% 13.75/5.41  tff(c_29683, plain, (![B_1766]: (v1_funct_2('#skF_3', '#skF_3', B_1766) | k1_relset_1('#skF_3', B_1766, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_29044, c_29677])).
% 13.75/5.41  tff(c_30559, plain, (![B_1766]: (v1_funct_2('#skF_3', '#skF_3', B_1766))), inference(demodulation, [status(thm), theory('equality')], [c_29210, c_30481, c_29683])).
% 13.75/5.41  tff(c_29053, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_29037, c_162])).
% 13.75/5.41  tff(c_30563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30559, c_29053])).
% 13.75/5.41  tff(c_30564, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_82])).
% 13.75/5.41  tff(c_31671, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski(k1_relat_1('#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_31650, c_30564])).
% 13.75/5.41  tff(c_31688, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30727, c_31103, c_31671])).
% 13.75/5.41  tff(c_31697, plain, (~v4_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34, c_31688])).
% 13.75/5.41  tff(c_31706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30727, c_30965, c_31697])).
% 13.75/5.41  tff(c_31708, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_72])).
% 13.75/5.41  tff(c_31728, plain, (![A_1984]: (k2_zfmisc_1(A_1984, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31708, c_31708, c_22])).
% 13.75/5.41  tff(c_31732, plain, (v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_31728, c_36])).
% 13.75/5.41  tff(c_32082, plain, (![B_2019, A_2020]: (v1_relat_1(B_2019) | ~m1_subset_1(B_2019, k1_zfmisc_1(A_2020)) | ~v1_relat_1(A_2020))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.75/5.41  tff(c_32088, plain, (![A_37]: (v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(k2_zfmisc_1(A_37, A_37)))), inference(resolution, [status(thm)], [c_56, c_32082])).
% 13.75/5.41  tff(c_32099, plain, (![A_2021]: (v1_relat_1(k6_relat_1(A_2021)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32088])).
% 13.75/5.41  tff(c_40, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.75/5.41  tff(c_31824, plain, (![A_23]: (k1_relat_1(A_23)!='#skF_4' | A_23='#skF_4' | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_31708, c_31708, c_40])).
% 13.75/5.41  tff(c_32102, plain, (![A_2021]: (k1_relat_1(k6_relat_1(A_2021))!='#skF_4' | k6_relat_1(A_2021)='#skF_4')), inference(resolution, [status(thm)], [c_32099, c_31824])).
% 13.75/5.41  tff(c_32109, plain, (![A_2021]: (A_2021!='#skF_4' | k6_relat_1(A_2021)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32102])).
% 13.75/5.41  tff(c_31746, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31708, c_31708, c_24])).
% 13.75/5.41  tff(c_32342, plain, (![C_2049, A_2050, B_2051]: (v4_relat_1(C_2049, A_2050) | ~m1_subset_1(C_2049, k1_zfmisc_1(k2_zfmisc_1(A_2050, B_2051))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 13.75/5.41  tff(c_32359, plain, (![C_2052]: (v4_relat_1(C_2052, '#skF_4') | ~m1_subset_1(C_2052, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_31746, c_32342])).
% 13.75/5.41  tff(c_32370, plain, (![A_2053]: (v4_relat_1(A_2053, '#skF_4') | ~r1_tarski(A_2053, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_32359])).
% 13.75/5.41  tff(c_32097, plain, (![A_37]: (v1_relat_1(k6_relat_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32088])).
% 13.75/5.41  tff(c_32266, plain, (![B_2043, A_2044]: (r1_tarski(k1_relat_1(B_2043), A_2044) | ~v4_relat_1(B_2043, A_2044) | ~v1_relat_1(B_2043))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.75/5.41  tff(c_32283, plain, (![A_24, A_2044]: (r1_tarski(A_24, A_2044) | ~v4_relat_1(k6_relat_1(A_24), A_2044) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_32266])).
% 13.75/5.41  tff(c_32291, plain, (![A_24, A_2044]: (r1_tarski(A_24, A_2044) | ~v4_relat_1(k6_relat_1(A_24), A_2044))), inference(demodulation, [status(thm), theory('equality')], [c_32097, c_32283])).
% 13.75/5.41  tff(c_32482, plain, (![A_2075]: (r1_tarski(A_2075, '#skF_4') | ~r1_tarski(k6_relat_1(A_2075), '#skF_4'))), inference(resolution, [status(thm)], [c_32370, c_32291])).
% 13.75/5.41  tff(c_32488, plain, (![A_2021]: (r1_tarski(A_2021, '#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | A_2021!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32109, c_32482])).
% 13.75/5.41  tff(c_32493, plain, (![A_2076]: (r1_tarski(A_2076, '#skF_4') | A_2076!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32488])).
% 13.75/5.41  tff(c_32098, plain, (![A_14, B_15]: (v1_relat_1(A_14) | ~v1_relat_1(B_15) | ~r1_tarski(A_14, B_15))), inference(resolution, [status(thm)], [c_28, c_32082])).
% 13.75/5.41  tff(c_32509, plain, (![A_2076]: (v1_relat_1(A_2076) | ~v1_relat_1('#skF_4') | A_2076!='#skF_4')), inference(resolution, [status(thm)], [c_32493, c_32098])).
% 13.75/5.41  tff(c_32520, plain, (![A_2076]: (v1_relat_1(A_2076) | A_2076!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31732, c_32509])).
% 13.75/5.41  tff(c_31727, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31708, c_31708, c_22])).
% 13.75/5.41  tff(c_32383, plain, (![C_2054, A_2055]: (v4_relat_1(C_2054, A_2055) | ~m1_subset_1(C_2054, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_31727, c_32342])).
% 13.75/5.41  tff(c_32462, plain, (![A_2067, A_2068]: (v4_relat_1(A_2067, A_2068) | ~r1_tarski(A_2067, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_32383])).
% 13.75/5.41  tff(c_32682, plain, (![A_2091, A_2092]: (r1_tarski(A_2091, A_2092) | ~r1_tarski(k6_relat_1(A_2091), '#skF_4'))), inference(resolution, [status(thm)], [c_32462, c_32291])).
% 13.75/5.41  tff(c_32693, plain, (![A_2021, A_2092]: (r1_tarski(A_2021, A_2092) | ~r1_tarski('#skF_4', '#skF_4') | A_2021!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_32109, c_32682])).
% 13.75/5.41  tff(c_32698, plain, (![A_2021, A_2092]: (r1_tarski(A_2021, A_2092) | A_2021!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_32693])).
% 13.75/5.41  tff(c_32975, plain, (![A_2135, A_2136, B_2137]: (v4_relat_1(A_2135, A_2136) | ~r1_tarski(A_2135, k2_zfmisc_1(A_2136, B_2137)))), inference(resolution, [status(thm)], [c_28, c_32342])).
% 13.75/5.41  tff(c_33006, plain, (![A_2021, A_2136]: (v4_relat_1(A_2021, A_2136) | A_2021!='#skF_4')), inference(resolution, [status(thm)], [c_32698, c_32975])).
% 13.75/5.41  tff(c_31707, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_72])).
% 13.75/5.41  tff(c_31714, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31708, c_31707])).
% 13.75/5.41  tff(c_31709, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31707, c_12])).
% 13.75/5.41  tff(c_31725, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_31714, c_31709])).
% 13.75/5.41  tff(c_31939, plain, (![A_2004, B_2005]: (r2_hidden('#skF_2'(A_2004, B_2005), A_2004) | r1_tarski(A_2004, B_2005))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.75/5.41  tff(c_31944, plain, (![A_2006, B_2007]: (~v1_xboole_0(A_2006) | r1_tarski(A_2006, B_2007))), inference(resolution, [status(thm)], [c_31939, c_2])).
% 13.75/5.41  tff(c_31766, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31727, c_31714, c_76])).
% 13.75/5.41  tff(c_31773, plain, (![A_1992, B_1993]: (r1_tarski(A_1992, B_1993) | ~m1_subset_1(A_1992, k1_zfmisc_1(B_1993)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.75/5.41  tff(c_31781, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_31766, c_31773])).
% 13.75/5.41  tff(c_31835, plain, (![B_1998, A_1999]: (B_1998=A_1999 | ~r1_tarski(B_1998, A_1999) | ~r1_tarski(A_1999, B_1998))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.75/5.41  tff(c_31848, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_31781, c_31835])).
% 13.75/5.41  tff(c_31854, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitLeft, [status(thm)], [c_31848])).
% 13.75/5.41  tff(c_31947, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_31944, c_31854])).
% 13.75/5.41  tff(c_31953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31725, c_31947])).
% 13.75/5.41  tff(c_31954, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_31848])).
% 13.75/5.41  tff(c_31959, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31954, c_31766])).
% 13.75/5.41  tff(c_32389, plain, (![A_2055]: (v4_relat_1('#skF_4', A_2055))), inference(resolution, [status(thm)], [c_31959, c_32383])).
% 13.75/5.41  tff(c_31990, plain, (![B_2012, A_2013]: (v1_relat_1(B_2012) | ~m1_subset_1(B_2012, k1_zfmisc_1(A_2013)) | ~v1_relat_1(A_2013))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.75/5.41  tff(c_31999, plain, (![A_37]: (v1_relat_1(k6_relat_1(A_37)) | ~v1_relat_1(k2_zfmisc_1(A_37, A_37)))), inference(resolution, [status(thm)], [c_56, c_31990])).
% 13.75/5.41  tff(c_32015, plain, (![A_2014]: (v1_relat_1(k6_relat_1(A_2014)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_31999])).
% 13.75/5.41  tff(c_32018, plain, (![A_2014]: (k1_relat_1(k6_relat_1(A_2014))!='#skF_4' | k6_relat_1(A_2014)='#skF_4')), inference(resolution, [status(thm)], [c_32015, c_31824])).
% 13.75/5.41  tff(c_32027, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32018])).
% 13.75/5.41  tff(c_31793, plain, (![A_1995]: (m1_subset_1(k6_relat_1(A_1995), k1_zfmisc_1(k2_zfmisc_1(A_1995, A_1995))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 13.75/5.41  tff(c_31800, plain, (m1_subset_1(k6_relat_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_31746, c_31793])).
% 13.75/5.41  tff(c_31809, plain, (r1_tarski(k6_relat_1('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_31800, c_26])).
% 13.75/5.41  tff(c_31847, plain, (k6_relat_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k6_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_31809, c_31835])).
% 13.75/5.41  tff(c_31976, plain, (~r1_tarski('#skF_4', k6_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_31847])).
% 13.75/5.41  tff(c_32028, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32027, c_31976])).
% 13.75/5.41  tff(c_32033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_32028])).
% 13.75/5.41  tff(c_32034, plain, (k6_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_31847])).
% 13.75/5.41  tff(c_32049, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_32034, c_42])).
% 13.75/5.41  tff(c_32280, plain, (![A_2044]: (r1_tarski('#skF_4', A_2044) | ~v4_relat_1('#skF_4', A_2044) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_32049, c_32266])).
% 13.75/5.41  tff(c_32289, plain, (![A_2044]: (r1_tarski('#skF_4', A_2044) | ~v4_relat_1('#skF_4', A_2044))), inference(demodulation, [status(thm), theory('equality')], [c_31732, c_32280])).
% 13.75/5.41  tff(c_32397, plain, (![A_2057]: (r1_tarski('#skF_4', A_2057))), inference(demodulation, [status(thm), theory('equality')], [c_32389, c_32289])).
% 13.75/5.41  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.75/5.41  tff(c_32432, plain, (![A_2063]: (A_2063='#skF_4' | ~r1_tarski(A_2063, '#skF_4'))), inference(resolution, [status(thm)], [c_32397, c_14])).
% 13.75/5.41  tff(c_33415, plain, (![B_2173]: (k1_relat_1(B_2173)='#skF_4' | ~v4_relat_1(B_2173, '#skF_4') | ~v1_relat_1(B_2173))), inference(resolution, [status(thm)], [c_34, c_32432])).
% 13.75/5.41  tff(c_33470, plain, (![A_2174]: (k1_relat_1(A_2174)='#skF_4' | ~v1_relat_1(A_2174) | A_2174!='#skF_4')), inference(resolution, [status(thm)], [c_33006, c_33415])).
% 13.75/5.41  tff(c_33488, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_32520, c_33470])).
% 13.75/5.41  tff(c_32598, plain, (![A_2082, B_2083, C_2084]: (k1_relset_1(A_2082, B_2083, C_2084)=k1_relat_1(C_2084) | ~m1_subset_1(C_2084, k1_zfmisc_1(k2_zfmisc_1(A_2082, B_2083))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 13.75/5.41  tff(c_34075, plain, (![B_2213, C_2214]: (k1_relset_1('#skF_4', B_2213, C_2214)=k1_relat_1(C_2214) | ~m1_subset_1(C_2214, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_31746, c_32598])).
% 13.75/5.41  tff(c_34077, plain, (![B_2213]: (k1_relset_1('#skF_4', B_2213, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_31959, c_34075])).
% 13.75/5.41  tff(c_34082, plain, (![B_2213]: (k1_relset_1('#skF_4', B_2213, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33488, c_34077])).
% 13.75/5.41  tff(c_32963, plain, (![C_2129, B_2130]: (v1_funct_2(C_2129, '#skF_4', B_2130) | k1_relset_1('#skF_4', B_2130, C_2129)!='#skF_4' | ~m1_subset_1(C_2129, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_31708, c_31708, c_31708, c_31708, c_84])).
% 13.75/5.41  tff(c_33012, plain, (![B_2138]: (v1_funct_2('#skF_4', '#skF_4', B_2138) | k1_relset_1('#skF_4', B_2138, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_31959, c_32963])).
% 13.75/5.41  tff(c_31811, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31714, c_31766, c_31746, c_31714, c_82])).
% 13.75/5.41  tff(c_31956, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_31954, c_31811])).
% 13.75/5.41  tff(c_33028, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_33012, c_31956])).
% 13.75/5.41  tff(c_34088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34082, c_33028])).
% 13.75/5.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.75/5.41  
% 13.75/5.41  Inference rules
% 13.75/5.41  ----------------------
% 13.75/5.41  #Ref     : 29
% 13.75/5.41  #Sup     : 7525
% 13.75/5.41  #Fact    : 0
% 13.75/5.41  #Define  : 0
% 13.75/5.41  #Split   : 105
% 13.75/5.41  #Chain   : 0
% 13.75/5.41  #Close   : 0
% 13.75/5.41  
% 13.75/5.41  Ordering : KBO
% 13.75/5.41  
% 13.75/5.41  Simplification rules
% 13.75/5.41  ----------------------
% 13.75/5.41  #Subsume      : 3066
% 13.75/5.41  #Demod        : 4511
% 13.75/5.41  #Tautology    : 2898
% 13.75/5.41  #SimpNegUnit  : 421
% 13.75/5.41  #BackRed      : 381
% 13.75/5.41  
% 13.75/5.41  #Partial instantiations: 0
% 13.75/5.41  #Strategies tried      : 1
% 13.75/5.41  
% 13.75/5.41  Timing (in seconds)
% 13.75/5.41  ----------------------
% 13.75/5.41  Preprocessing        : 0.37
% 13.75/5.41  Parsing              : 0.19
% 13.75/5.41  CNF conversion       : 0.03
% 13.75/5.41  Main loop            : 4.20
% 13.75/5.41  Inferencing          : 1.15
% 13.75/5.41  Reduction            : 1.57
% 13.75/5.41  Demodulation         : 1.11
% 13.75/5.41  BG Simplification    : 0.10
% 13.75/5.41  Subsumption          : 1.10
% 13.75/5.41  Abstraction          : 0.14
% 13.75/5.41  MUC search           : 0.00
% 13.75/5.41  Cooper               : 0.00
% 13.75/5.41  Total                : 4.68
% 13.75/5.41  Index Insertion      : 0.00
% 13.75/5.41  Index Deletion       : 0.00
% 13.75/5.41  Index Matching       : 0.00
% 13.75/5.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
