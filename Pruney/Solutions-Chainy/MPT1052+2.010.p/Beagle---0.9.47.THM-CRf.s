%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:10 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 501 expanded)
%              Number of leaves         :   36 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 (1009 expanded)
%              Number of equality atoms :   45 ( 204 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3616,plain,(
    ! [B_1294,A_1295] :
      ( r1_tarski(k2_relat_1(B_1294),A_1295)
      | ~ v5_relat_1(B_1294,A_1295)
      | ~ v1_relat_1(B_1294) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_120,plain,(
    ! [A_37,B_38] :
      ( v1_xboole_0(k1_funct_2(A_37,B_38))
      | ~ v1_xboole_0(B_38)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_127,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_91])).

tff(c_136,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_48,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_92,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_181,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_funct_2(C_50,A_51,B_52)
      | ~ r2_hidden(C_50,k1_funct_2(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_193,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_181])).

tff(c_40,plain,(
    ! [C_23,A_21,B_22] :
      ( m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ r2_hidden(C_23,k1_funct_2(A_21,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_543,plain,(
    ! [A_101,B_102,C_103] :
      ( k1_relset_1(A_101,B_102,C_103) = k1_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1042,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ r2_hidden(C_121,k1_funct_2(A_119,B_120)) ) ),
    inference(resolution,[status(thm)],[c_40,c_543])).

tff(c_1081,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1042])).

tff(c_1725,plain,(
    ! [B_143,A_144,C_145] :
      ( k1_xboole_0 = B_143
      | k1_relset_1(A_144,B_143,C_145) = A_144
      | ~ v1_funct_2(C_145,A_144,B_143)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2366,plain,(
    ! [B_1175,A_1176,C_1177] :
      ( k1_xboole_0 = B_1175
      | k1_relset_1(A_1176,B_1175,C_1177) = A_1176
      | ~ v1_funct_2(C_1177,A_1176,B_1175)
      | ~ r2_hidden(C_1177,k1_funct_2(A_1176,B_1175)) ) ),
    inference(resolution,[status(thm)],[c_40,c_1725])).

tff(c_2409,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2366])).

tff(c_2419,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_1081,c_2409])).

tff(c_2420,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2419])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2479,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2420,c_6])).

tff(c_2481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_2479])).

tff(c_2483,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2491,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2483,c_8])).

tff(c_2482,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_2487,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2482,c_8])).

tff(c_2502,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2491,c_2487])).

tff(c_2508,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2502,c_92])).

tff(c_2510,plain,(
    r2_hidden('#skF_4',k1_funct_2('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2502,c_50])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2495,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_2',B_7) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2487,c_2487,c_14])).

tff(c_2539,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_3',B_7) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2502,c_2502,c_2495])).

tff(c_2811,plain,(
    ! [C_1212,A_1213,B_1214] :
      ( m1_subset_1(C_1212,k1_zfmisc_1(k2_zfmisc_1(A_1213,B_1214)))
      | ~ r2_hidden(C_1212,k1_funct_2(A_1213,B_1214)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2958,plain,(
    ! [C_1229,B_1230] :
      ( m1_subset_1(C_1229,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(C_1229,k1_funct_2('#skF_3',B_1230)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2539,c_2811])).

tff(c_2978,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2510,c_2958])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2494,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2487,c_2487,c_12])).

tff(c_2527,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2502,c_2502,c_2494])).

tff(c_2947,plain,(
    ! [A_1226,B_1227,C_1228] :
      ( k1_relset_1(A_1226,B_1227,C_1228) = k1_relat_1(C_1228)
      | ~ m1_subset_1(C_1228,k1_zfmisc_1(k2_zfmisc_1(A_1226,B_1227))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3074,plain,(
    ! [A_1246,C_1247] :
      ( k1_relset_1(A_1246,'#skF_3',C_1247) = k1_relat_1(C_1247)
      | ~ m1_subset_1(C_1247,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2527,c_2947])).

tff(c_3080,plain,(
    ! [A_1246] : k1_relset_1(A_1246,'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2978,c_3074])).

tff(c_2585,plain,(
    ! [C_1191,A_1192,B_1193] :
      ( v1_funct_2(C_1191,A_1192,B_1193)
      | ~ r2_hidden(C_1191,k1_funct_2(A_1192,B_1193)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2593,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2510,c_2585])).

tff(c_34,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_55,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_34])).

tff(c_3439,plain,(
    ! [B_1267,C_1268] :
      ( k1_relset_1('#skF_3',B_1267,C_1268) = '#skF_3'
      | ~ v1_funct_2(C_1268,'#skF_3',B_1267)
      | ~ m1_subset_1(C_1268,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2491,c_2491,c_2491,c_2491,c_55])).

tff(c_3447,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2593,c_3439])).

tff(c_3453,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2978,c_3080,c_3447])).

tff(c_3455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2508,c_3453])).

tff(c_3456,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3622,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3616,c_3456])).

tff(c_3626,plain,(
    ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3622])).

tff(c_3659,plain,(
    ! [C_1308,A_1309,B_1310] :
      ( m1_subset_1(C_1308,k1_zfmisc_1(k2_zfmisc_1(A_1309,B_1310)))
      | ~ r2_hidden(C_1308,k1_funct_2(A_1309,B_1310)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_20,plain,(
    ! [C_12,B_11,A_10] :
      ( v5_relat_1(C_12,B_11)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3694,plain,(
    ! [C_1315,B_1316,A_1317] :
      ( v5_relat_1(C_1315,B_1316)
      | ~ r2_hidden(C_1315,k1_funct_2(A_1317,B_1316)) ) ),
    inference(resolution,[status(thm)],[c_3659,c_20])).

tff(c_3710,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_3694])).

tff(c_3715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3626,c_3710])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:25:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.95  
% 4.85/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.95  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.85/1.95  
% 4.85/1.95  %Foreground sorts:
% 4.85/1.95  
% 4.85/1.95  
% 4.85/1.95  %Background operators:
% 4.85/1.95  
% 4.85/1.95  
% 4.85/1.95  %Foreground operators:
% 4.85/1.95  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 4.85/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.85/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.85/1.95  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.85/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.85/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.85/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.85/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.85/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.85/1.95  tff('#skF_3', type, '#skF_3': $i).
% 4.85/1.95  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.85/1.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.85/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.85/1.95  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 4.85/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.85/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.85/1.95  tff('#skF_4', type, '#skF_4': $i).
% 4.85/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/1.95  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.85/1.95  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 4.85/1.95  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.85/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.85/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.85/1.95  
% 4.85/1.97  tff(f_104, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_2)).
% 4.85/1.97  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.85/1.97  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_2)).
% 4.85/1.97  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.85/1.97  tff(f_91, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 4.85/1.97  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.85/1.97  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.85/1.97  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.85/1.97  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.85/1.97  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.85/1.97  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.85/1.97  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.85/1.97  tff(c_3616, plain, (![B_1294, A_1295]: (r1_tarski(k2_relat_1(B_1294), A_1295) | ~v5_relat_1(B_1294, A_1295) | ~v1_relat_1(B_1294))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.85/1.97  tff(c_120, plain, (![A_37, B_38]: (v1_xboole_0(k1_funct_2(A_37, B_38)) | ~v1_xboole_0(B_38) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.85/1.97  tff(c_50, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.85/1.97  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.85/1.97  tff(c_91, plain, (~v1_xboole_0(k1_funct_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_2])).
% 4.85/1.97  tff(c_127, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_120, c_91])).
% 4.85/1.97  tff(c_136, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_127])).
% 4.85/1.97  tff(c_48, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | k1_relat_1('#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.85/1.97  tff(c_92, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_48])).
% 4.85/1.97  tff(c_181, plain, (![C_50, A_51, B_52]: (v1_funct_2(C_50, A_51, B_52) | ~r2_hidden(C_50, k1_funct_2(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.85/1.97  tff(c_193, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_181])).
% 4.85/1.97  tff(c_40, plain, (![C_23, A_21, B_22]: (m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~r2_hidden(C_23, k1_funct_2(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.85/1.97  tff(c_543, plain, (![A_101, B_102, C_103]: (k1_relset_1(A_101, B_102, C_103)=k1_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.85/1.97  tff(c_1042, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~r2_hidden(C_121, k1_funct_2(A_119, B_120)))), inference(resolution, [status(thm)], [c_40, c_543])).
% 4.85/1.97  tff(c_1081, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1042])).
% 4.85/1.97  tff(c_1725, plain, (![B_143, A_144, C_145]: (k1_xboole_0=B_143 | k1_relset_1(A_144, B_143, C_145)=A_144 | ~v1_funct_2(C_145, A_144, B_143) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.85/1.97  tff(c_2366, plain, (![B_1175, A_1176, C_1177]: (k1_xboole_0=B_1175 | k1_relset_1(A_1176, B_1175, C_1177)=A_1176 | ~v1_funct_2(C_1177, A_1176, B_1175) | ~r2_hidden(C_1177, k1_funct_2(A_1176, B_1175)))), inference(resolution, [status(thm)], [c_40, c_1725])).
% 4.85/1.97  tff(c_2409, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_2366])).
% 4.85/1.97  tff(c_2419, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_1081, c_2409])).
% 4.85/1.97  tff(c_2420, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_92, c_2419])).
% 4.85/1.97  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.85/1.97  tff(c_2479, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2420, c_6])).
% 4.85/1.97  tff(c_2481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_2479])).
% 4.85/1.97  tff(c_2483, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_127])).
% 4.85/1.97  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.85/1.97  tff(c_2491, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2483, c_8])).
% 4.85/1.97  tff(c_2482, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_127])).
% 4.85/1.97  tff(c_2487, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2482, c_8])).
% 4.85/1.97  tff(c_2502, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2491, c_2487])).
% 4.85/1.97  tff(c_2508, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2502, c_92])).
% 4.85/1.97  tff(c_2510, plain, (r2_hidden('#skF_4', k1_funct_2('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2502, c_50])).
% 4.85/1.97  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.85/1.97  tff(c_2495, plain, (![B_7]: (k2_zfmisc_1('#skF_2', B_7)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2487, c_2487, c_14])).
% 4.85/1.97  tff(c_2539, plain, (![B_7]: (k2_zfmisc_1('#skF_3', B_7)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2502, c_2502, c_2495])).
% 4.85/1.97  tff(c_2811, plain, (![C_1212, A_1213, B_1214]: (m1_subset_1(C_1212, k1_zfmisc_1(k2_zfmisc_1(A_1213, B_1214))) | ~r2_hidden(C_1212, k1_funct_2(A_1213, B_1214)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.85/1.97  tff(c_2958, plain, (![C_1229, B_1230]: (m1_subset_1(C_1229, k1_zfmisc_1('#skF_3')) | ~r2_hidden(C_1229, k1_funct_2('#skF_3', B_1230)))), inference(superposition, [status(thm), theory('equality')], [c_2539, c_2811])).
% 4.85/1.97  tff(c_2978, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_2510, c_2958])).
% 4.85/1.97  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.85/1.97  tff(c_2494, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2487, c_2487, c_12])).
% 4.85/1.97  tff(c_2527, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2502, c_2502, c_2494])).
% 4.85/1.97  tff(c_2947, plain, (![A_1226, B_1227, C_1228]: (k1_relset_1(A_1226, B_1227, C_1228)=k1_relat_1(C_1228) | ~m1_subset_1(C_1228, k1_zfmisc_1(k2_zfmisc_1(A_1226, B_1227))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.85/1.97  tff(c_3074, plain, (![A_1246, C_1247]: (k1_relset_1(A_1246, '#skF_3', C_1247)=k1_relat_1(C_1247) | ~m1_subset_1(C_1247, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2527, c_2947])).
% 4.85/1.97  tff(c_3080, plain, (![A_1246]: (k1_relset_1(A_1246, '#skF_3', '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2978, c_3074])).
% 4.85/1.97  tff(c_2585, plain, (![C_1191, A_1192, B_1193]: (v1_funct_2(C_1191, A_1192, B_1193) | ~r2_hidden(C_1191, k1_funct_2(A_1192, B_1193)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.85/1.97  tff(c_2593, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2510, c_2585])).
% 4.85/1.97  tff(c_34, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.85/1.97  tff(c_55, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_34])).
% 4.85/1.97  tff(c_3439, plain, (![B_1267, C_1268]: (k1_relset_1('#skF_3', B_1267, C_1268)='#skF_3' | ~v1_funct_2(C_1268, '#skF_3', B_1267) | ~m1_subset_1(C_1268, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2491, c_2491, c_2491, c_2491, c_55])).
% 4.85/1.97  tff(c_3447, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_2593, c_3439])).
% 4.85/1.97  tff(c_3453, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2978, c_3080, c_3447])).
% 4.85/1.97  tff(c_3455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2508, c_3453])).
% 4.85/1.97  tff(c_3456, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 4.85/1.97  tff(c_3622, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3616, c_3456])).
% 4.85/1.97  tff(c_3626, plain, (~v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3622])).
% 4.85/1.97  tff(c_3659, plain, (![C_1308, A_1309, B_1310]: (m1_subset_1(C_1308, k1_zfmisc_1(k2_zfmisc_1(A_1309, B_1310))) | ~r2_hidden(C_1308, k1_funct_2(A_1309, B_1310)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.85/1.97  tff(c_20, plain, (![C_12, B_11, A_10]: (v5_relat_1(C_12, B_11) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.85/1.97  tff(c_3694, plain, (![C_1315, B_1316, A_1317]: (v5_relat_1(C_1315, B_1316) | ~r2_hidden(C_1315, k1_funct_2(A_1317, B_1316)))), inference(resolution, [status(thm)], [c_3659, c_20])).
% 4.85/1.97  tff(c_3710, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_3694])).
% 4.85/1.97  tff(c_3715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3626, c_3710])).
% 4.85/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.97  
% 4.85/1.97  Inference rules
% 4.85/1.97  ----------------------
% 4.85/1.97  #Ref     : 0
% 4.85/1.97  #Sup     : 903
% 4.85/1.97  #Fact    : 4
% 4.85/1.97  #Define  : 0
% 4.85/1.97  #Split   : 15
% 4.85/1.97  #Chain   : 0
% 4.85/1.97  #Close   : 0
% 4.85/1.97  
% 4.85/1.97  Ordering : KBO
% 4.85/1.97  
% 4.85/1.97  Simplification rules
% 4.85/1.97  ----------------------
% 4.85/1.97  #Subsume      : 242
% 4.85/1.97  #Demod        : 378
% 4.85/1.97  #Tautology    : 331
% 4.85/1.97  #SimpNegUnit  : 31
% 4.85/1.97  #BackRed      : 69
% 4.85/1.97  
% 4.85/1.97  #Partial instantiations: 171
% 4.85/1.97  #Strategies tried      : 1
% 4.85/1.97  
% 4.85/1.97  Timing (in seconds)
% 4.85/1.97  ----------------------
% 4.85/1.97  Preprocessing        : 0.37
% 4.85/1.97  Parsing              : 0.19
% 4.85/1.97  CNF conversion       : 0.03
% 4.85/1.97  Main loop            : 0.82
% 4.85/1.97  Inferencing          : 0.31
% 4.85/1.97  Reduction            : 0.24
% 4.85/1.97  Demodulation         : 0.17
% 4.85/1.97  BG Simplification    : 0.04
% 4.85/1.97  Subsumption          : 0.17
% 4.85/1.97  Abstraction          : 0.04
% 4.85/1.97  MUC search           : 0.00
% 4.85/1.97  Cooper               : 0.00
% 4.85/1.97  Total                : 1.23
% 4.85/1.97  Index Insertion      : 0.00
% 4.85/1.97  Index Deletion       : 0.00
% 4.85/1.97  Index Matching       : 0.00
% 4.85/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
