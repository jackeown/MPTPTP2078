%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:43 EST 2020

% Result     : Theorem 6.84s
% Output     : CNFRefutation 6.93s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 347 expanded)
%              Number of leaves         :   54 ( 138 expanded)
%              Depth                    :   14
%              Number of atoms          :  186 ( 675 expanded)
%              Number of equality atoms :   60 ( 161 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_164,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_152,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_140,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_143,plain,(
    ! [C_97,A_98,B_99] :
      ( v1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_156,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_143])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_54] :
      ( k2_relat_1(A_54) = k1_xboole_0
      | k1_relat_1(A_54) != k1_xboole_0
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_160,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_156,c_58])).

tff(c_178,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_499,plain,(
    ! [A_164] :
      ( k1_relat_1(A_164) = k1_xboole_0
      | k2_relat_1(A_164) != k1_xboole_0
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_505,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_156,c_499])).

tff(c_509,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_505])).

tff(c_796,plain,(
    ! [C_206,A_207,B_208] :
      ( v4_relat_1(C_206,A_207)
      | ~ m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_811,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_84,c_796])).

tff(c_52,plain,(
    ! [B_49,A_48] :
      ( k7_relat_1(B_49,A_48) = B_49
      | ~ v4_relat_1(B_49,A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_814,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_811,c_52])).

tff(c_817,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_814])).

tff(c_46,plain,(
    ! [B_45,A_44] :
      ( k2_relat_1(k7_relat_1(B_45,A_44)) = k9_relat_1(B_45,A_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_821,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_817,c_46])).

tff(c_825,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_821])).

tff(c_40,plain,(
    ! [A_39,B_41] :
      ( k9_relat_1(A_39,k1_tarski(B_41)) = k11_relat_1(A_39,B_41)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_830,plain,
    ( k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_40])).

tff(c_837,plain,(
    k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_830])).

tff(c_48,plain,(
    ! [A_46,B_47] :
      ( r2_hidden(A_46,k1_relat_1(B_47))
      | k11_relat_1(B_47,A_46) = k1_xboole_0
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1449,plain,(
    ! [A_285,B_286,C_287] :
      ( k1_relset_1(A_285,B_286,C_287) = k1_relat_1(C_287)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1464,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_1449])).

tff(c_1757,plain,(
    ! [A_320,B_321,C_322] :
      ( m1_subset_1(k1_relset_1(A_320,B_321,C_322),k1_zfmisc_1(A_320))
      | ~ m1_subset_1(C_322,k1_zfmisc_1(k2_zfmisc_1(A_320,B_321))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1801,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1464,c_1757])).

tff(c_1820,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1801])).

tff(c_36,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1824,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1820,c_36])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1151,plain,(
    ! [A_257,B_258,C_259] :
      ( r1_tarski(k2_tarski(A_257,B_258),C_259)
      | ~ r2_hidden(B_258,C_259)
      | ~ r2_hidden(A_257,C_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1200,plain,(
    ! [A_260,C_261] :
      ( r1_tarski(k1_tarski(A_260),C_261)
      | ~ r2_hidden(A_260,C_261)
      | ~ r2_hidden(A_260,C_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1151])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1238,plain,(
    ! [A_260,C_261] :
      ( k1_tarski(A_260) = C_261
      | ~ r1_tarski(C_261,k1_tarski(A_260))
      | ~ r2_hidden(A_260,C_261) ) ),
    inference(resolution,[status(thm)],[c_1200,c_2])).

tff(c_1837,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1824,c_1238])).

tff(c_1842,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1837])).

tff(c_1846,plain,
    ( k11_relat_1('#skF_4','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1842])).

tff(c_1849,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_837,c_1846])).

tff(c_1851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_509,c_1849])).

tff(c_1852,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1837])).

tff(c_1864,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_84])).

tff(c_2370,plain,(
    ! [D_356,C_357,B_358,A_359] :
      ( m1_subset_1(D_356,k1_zfmisc_1(k2_zfmisc_1(C_357,B_358)))
      | ~ r1_tarski(k2_relat_1(D_356),B_358)
      | ~ m1_subset_1(D_356,k1_zfmisc_1(k2_zfmisc_1(C_357,A_359))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2596,plain,(
    ! [B_377] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_377)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_377) ) ),
    inference(resolution,[status(thm)],[c_1864,c_2370])).

tff(c_74,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k7_relset_1(A_73,B_74,C_75,D_76) = k9_relat_1(C_75,D_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6043,plain,(
    ! [B_597,D_598] :
      ( k7_relset_1(k1_relat_1('#skF_4'),B_597,'#skF_4',D_598) = k9_relat_1('#skF_4',D_598)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_597) ) ),
    inference(resolution,[status(thm)],[c_2596,c_74])).

tff(c_6052,plain,(
    ! [D_599] : k7_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4',D_599) = k9_relat_1('#skF_4',D_599) ),
    inference(resolution,[status(thm)],[c_6,c_6043])).

tff(c_2393,plain,(
    ! [B_358] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),B_358)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_358) ) ),
    inference(resolution,[status(thm)],[c_1864,c_2370])).

tff(c_2096,plain,(
    ! [A_332,B_333,C_334,D_335] :
      ( m1_subset_1(k7_relset_1(A_332,B_333,C_334,D_335),k1_zfmisc_1(B_333))
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(A_332,B_333))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4177,plain,(
    ! [A_469,B_470,C_471,D_472] :
      ( r1_tarski(k7_relset_1(A_469,B_470,C_471,D_472),B_470)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(A_469,B_470))) ) ),
    inference(resolution,[status(thm)],[c_2096,c_36])).

tff(c_4200,plain,(
    ! [B_358,D_472] :
      ( r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),B_358,'#skF_4',D_472),B_358)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_358) ) ),
    inference(resolution,[status(thm)],[c_2393,c_4177])).

tff(c_6058,plain,(
    ! [D_599] :
      ( r1_tarski(k9_relat_1('#skF_4',D_599),k2_relat_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k2_relat_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6052,c_4200])).

tff(c_6067,plain,(
    ! [D_599] : r1_tarski(k9_relat_1('#skF_4',D_599),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6058])).

tff(c_88,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_60,plain,(
    ! [B_56,A_55] :
      ( k1_tarski(k1_funct_1(B_56,A_55)) = k2_relat_1(B_56)
      | k1_tarski(A_55) != k1_relat_1(B_56)
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1963,plain,(
    ! [D_76] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_76) = k9_relat_1('#skF_4',D_76) ),
    inference(resolution,[status(thm)],[c_1864,c_74])).

tff(c_80,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1863,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_80])).

tff(c_2311,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1963,c_1863])).

tff(c_2406,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_2311])).

tff(c_2408,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_88,c_1852,c_2406])).

tff(c_6071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6067,c_2408])).

tff(c_6072,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_6073,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_6719,plain,(
    ! [B_703,A_704] :
      ( v4_relat_1(B_703,A_704)
      | ~ r1_tarski(k1_relat_1(B_703),A_704)
      | ~ v1_relat_1(B_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6725,plain,(
    ! [A_704] :
      ( v4_relat_1('#skF_4',A_704)
      | ~ r1_tarski(k1_xboole_0,A_704)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6073,c_6719])).

tff(c_6733,plain,(
    ! [A_704] : v4_relat_1('#skF_4',A_704) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_8,c_6725])).

tff(c_6935,plain,(
    ! [B_738,A_739] :
      ( k7_relat_1(B_738,A_739) = B_738
      | ~ v4_relat_1(B_738,A_739)
      | ~ v1_relat_1(B_738) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6950,plain,(
    ! [A_704] :
      ( k7_relat_1('#skF_4',A_704) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6733,c_6935])).

tff(c_6961,plain,(
    ! [A_704] : k7_relat_1('#skF_4',A_704) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_6950])).

tff(c_7050,plain,(
    ! [B_746,A_747] :
      ( k2_relat_1(k7_relat_1(B_746,A_747)) = k9_relat_1(B_746,A_747)
      | ~ v1_relat_1(B_746) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7065,plain,(
    ! [A_704] :
      ( k9_relat_1('#skF_4',A_704) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6961,c_7050])).

tff(c_7071,plain,(
    ! [A_704] : k9_relat_1('#skF_4',A_704) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_6072,c_7065])).

tff(c_8334,plain,(
    ! [A_870,B_871,C_872,D_873] :
      ( k7_relset_1(A_870,B_871,C_872,D_873) = k9_relat_1(C_872,D_873)
      | ~ m1_subset_1(C_872,k1_zfmisc_1(k2_zfmisc_1(A_870,B_871))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_8348,plain,(
    ! [D_873] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_873) = k9_relat_1('#skF_4',D_873) ),
    inference(resolution,[status(thm)],[c_84,c_8334])).

tff(c_8359,plain,(
    ! [D_873] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_873) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7071,c_8348])).

tff(c_8372,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8359,c_80])).

tff(c_8375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.84/2.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.84/2.52  
% 6.84/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.84/2.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.84/2.52  
% 6.84/2.52  %Foreground sorts:
% 6.84/2.52  
% 6.84/2.52  
% 6.84/2.52  %Background operators:
% 6.84/2.52  
% 6.84/2.52  
% 6.84/2.52  %Foreground operators:
% 6.84/2.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.84/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.84/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.84/2.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.84/2.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.84/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.84/2.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.84/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.84/2.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.84/2.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.84/2.52  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.84/2.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.84/2.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.84/2.52  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 6.84/2.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.84/2.52  tff('#skF_2', type, '#skF_2': $i).
% 6.84/2.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.84/2.52  tff('#skF_3', type, '#skF_3': $i).
% 6.84/2.52  tff('#skF_1', type, '#skF_1': $i).
% 6.84/2.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.84/2.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.84/2.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.84/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.84/2.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.84/2.52  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.84/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.84/2.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.84/2.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.84/2.52  tff('#skF_4', type, '#skF_4': $i).
% 6.84/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.84/2.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.84/2.52  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.84/2.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.84/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.84/2.52  
% 6.93/2.54  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.93/2.54  tff(f_164, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 6.93/2.54  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.93/2.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.93/2.54  tff(f_106, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 6.93/2.54  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.93/2.54  tff(f_91, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 6.93/2.54  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 6.93/2.54  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 6.93/2.54  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 6.93/2.54  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.93/2.54  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 6.93/2.54  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.93/2.54  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.93/2.54  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.93/2.54  tff(f_152, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 6.93/2.54  tff(f_140, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.93/2.54  tff(f_132, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 6.93/2.54  tff(f_114, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 6.93/2.54  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 6.93/2.54  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.93/2.54  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.93/2.54  tff(c_143, plain, (![C_97, A_98, B_99]: (v1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.93/2.54  tff(c_156, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_143])).
% 6.93/2.54  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.93/2.54  tff(c_58, plain, (![A_54]: (k2_relat_1(A_54)=k1_xboole_0 | k1_relat_1(A_54)!=k1_xboole_0 | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.93/2.54  tff(c_160, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_156, c_58])).
% 6.93/2.54  tff(c_178, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_160])).
% 6.93/2.54  tff(c_499, plain, (![A_164]: (k1_relat_1(A_164)=k1_xboole_0 | k2_relat_1(A_164)!=k1_xboole_0 | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.93/2.54  tff(c_505, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_156, c_499])).
% 6.93/2.54  tff(c_509, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_178, c_505])).
% 6.93/2.54  tff(c_796, plain, (![C_206, A_207, B_208]: (v4_relat_1(C_206, A_207) | ~m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.93/2.54  tff(c_811, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_84, c_796])).
% 6.93/2.54  tff(c_52, plain, (![B_49, A_48]: (k7_relat_1(B_49, A_48)=B_49 | ~v4_relat_1(B_49, A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.93/2.54  tff(c_814, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_811, c_52])).
% 6.93/2.54  tff(c_817, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_814])).
% 6.93/2.54  tff(c_46, plain, (![B_45, A_44]: (k2_relat_1(k7_relat_1(B_45, A_44))=k9_relat_1(B_45, A_44) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.93/2.54  tff(c_821, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_817, c_46])).
% 6.93/2.54  tff(c_825, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_821])).
% 6.93/2.54  tff(c_40, plain, (![A_39, B_41]: (k9_relat_1(A_39, k1_tarski(B_41))=k11_relat_1(A_39, B_41) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.93/2.54  tff(c_830, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_825, c_40])).
% 6.93/2.54  tff(c_837, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_830])).
% 6.93/2.54  tff(c_48, plain, (![A_46, B_47]: (r2_hidden(A_46, k1_relat_1(B_47)) | k11_relat_1(B_47, A_46)=k1_xboole_0 | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.93/2.54  tff(c_1449, plain, (![A_285, B_286, C_287]: (k1_relset_1(A_285, B_286, C_287)=k1_relat_1(C_287) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 6.93/2.54  tff(c_1464, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_1449])).
% 6.93/2.54  tff(c_1757, plain, (![A_320, B_321, C_322]: (m1_subset_1(k1_relset_1(A_320, B_321, C_322), k1_zfmisc_1(A_320)) | ~m1_subset_1(C_322, k1_zfmisc_1(k2_zfmisc_1(A_320, B_321))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.93/2.54  tff(c_1801, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1464, c_1757])).
% 6.93/2.54  tff(c_1820, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1801])).
% 6.93/2.54  tff(c_36, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.93/2.54  tff(c_1824, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_1820, c_36])).
% 6.93/2.54  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.93/2.54  tff(c_1151, plain, (![A_257, B_258, C_259]: (r1_tarski(k2_tarski(A_257, B_258), C_259) | ~r2_hidden(B_258, C_259) | ~r2_hidden(A_257, C_259))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.93/2.54  tff(c_1200, plain, (![A_260, C_261]: (r1_tarski(k1_tarski(A_260), C_261) | ~r2_hidden(A_260, C_261) | ~r2_hidden(A_260, C_261))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1151])).
% 6.93/2.54  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.93/2.54  tff(c_1238, plain, (![A_260, C_261]: (k1_tarski(A_260)=C_261 | ~r1_tarski(C_261, k1_tarski(A_260)) | ~r2_hidden(A_260, C_261))), inference(resolution, [status(thm)], [c_1200, c_2])).
% 6.93/2.54  tff(c_1837, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | ~r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1824, c_1238])).
% 6.93/2.54  tff(c_1842, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1837])).
% 6.93/2.54  tff(c_1846, plain, (k11_relat_1('#skF_4', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1842])).
% 6.93/2.54  tff(c_1849, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_156, c_837, c_1846])).
% 6.93/2.54  tff(c_1851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_509, c_1849])).
% 6.93/2.54  tff(c_1852, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1837])).
% 6.93/2.54  tff(c_1864, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1852, c_84])).
% 6.93/2.54  tff(c_2370, plain, (![D_356, C_357, B_358, A_359]: (m1_subset_1(D_356, k1_zfmisc_1(k2_zfmisc_1(C_357, B_358))) | ~r1_tarski(k2_relat_1(D_356), B_358) | ~m1_subset_1(D_356, k1_zfmisc_1(k2_zfmisc_1(C_357, A_359))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.93/2.54  tff(c_2596, plain, (![B_377]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_377))) | ~r1_tarski(k2_relat_1('#skF_4'), B_377))), inference(resolution, [status(thm)], [c_1864, c_2370])).
% 6.93/2.54  tff(c_74, plain, (![A_73, B_74, C_75, D_76]: (k7_relset_1(A_73, B_74, C_75, D_76)=k9_relat_1(C_75, D_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.93/2.54  tff(c_6043, plain, (![B_597, D_598]: (k7_relset_1(k1_relat_1('#skF_4'), B_597, '#skF_4', D_598)=k9_relat_1('#skF_4', D_598) | ~r1_tarski(k2_relat_1('#skF_4'), B_597))), inference(resolution, [status(thm)], [c_2596, c_74])).
% 6.93/2.54  tff(c_6052, plain, (![D_599]: (k7_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4', D_599)=k9_relat_1('#skF_4', D_599))), inference(resolution, [status(thm)], [c_6, c_6043])).
% 6.93/2.54  tff(c_2393, plain, (![B_358]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), B_358))) | ~r1_tarski(k2_relat_1('#skF_4'), B_358))), inference(resolution, [status(thm)], [c_1864, c_2370])).
% 6.93/2.54  tff(c_2096, plain, (![A_332, B_333, C_334, D_335]: (m1_subset_1(k7_relset_1(A_332, B_333, C_334, D_335), k1_zfmisc_1(B_333)) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(A_332, B_333))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 6.93/2.54  tff(c_4177, plain, (![A_469, B_470, C_471, D_472]: (r1_tarski(k7_relset_1(A_469, B_470, C_471, D_472), B_470) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(A_469, B_470))))), inference(resolution, [status(thm)], [c_2096, c_36])).
% 6.93/2.54  tff(c_4200, plain, (![B_358, D_472]: (r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), B_358, '#skF_4', D_472), B_358) | ~r1_tarski(k2_relat_1('#skF_4'), B_358))), inference(resolution, [status(thm)], [c_2393, c_4177])).
% 6.93/2.54  tff(c_6058, plain, (![D_599]: (r1_tarski(k9_relat_1('#skF_4', D_599), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1('#skF_4'), k2_relat_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_6052, c_4200])).
% 6.93/2.54  tff(c_6067, plain, (![D_599]: (r1_tarski(k9_relat_1('#skF_4', D_599), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6058])).
% 6.93/2.54  tff(c_88, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.93/2.54  tff(c_60, plain, (![B_56, A_55]: (k1_tarski(k1_funct_1(B_56, A_55))=k2_relat_1(B_56) | k1_tarski(A_55)!=k1_relat_1(B_56) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.93/2.54  tff(c_1963, plain, (![D_76]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_76)=k9_relat_1('#skF_4', D_76))), inference(resolution, [status(thm)], [c_1864, c_74])).
% 6.93/2.54  tff(c_80, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 6.93/2.54  tff(c_1863, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1852, c_80])).
% 6.93/2.54  tff(c_2311, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1963, c_1863])).
% 6.93/2.54  tff(c_2406, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_60, c_2311])).
% 6.93/2.54  tff(c_2408, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_88, c_1852, c_2406])).
% 6.93/2.54  tff(c_6071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6067, c_2408])).
% 6.93/2.54  tff(c_6072, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_160])).
% 6.93/2.54  tff(c_6073, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_160])).
% 6.93/2.54  tff(c_6719, plain, (![B_703, A_704]: (v4_relat_1(B_703, A_704) | ~r1_tarski(k1_relat_1(B_703), A_704) | ~v1_relat_1(B_703))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.93/2.54  tff(c_6725, plain, (![A_704]: (v4_relat_1('#skF_4', A_704) | ~r1_tarski(k1_xboole_0, A_704) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6073, c_6719])).
% 6.93/2.54  tff(c_6733, plain, (![A_704]: (v4_relat_1('#skF_4', A_704))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_8, c_6725])).
% 6.93/2.54  tff(c_6935, plain, (![B_738, A_739]: (k7_relat_1(B_738, A_739)=B_738 | ~v4_relat_1(B_738, A_739) | ~v1_relat_1(B_738))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.93/2.54  tff(c_6950, plain, (![A_704]: (k7_relat_1('#skF_4', A_704)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_6733, c_6935])).
% 6.93/2.54  tff(c_6961, plain, (![A_704]: (k7_relat_1('#skF_4', A_704)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_6950])).
% 6.93/2.54  tff(c_7050, plain, (![B_746, A_747]: (k2_relat_1(k7_relat_1(B_746, A_747))=k9_relat_1(B_746, A_747) | ~v1_relat_1(B_746))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.93/2.54  tff(c_7065, plain, (![A_704]: (k9_relat_1('#skF_4', A_704)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6961, c_7050])).
% 6.93/2.54  tff(c_7071, plain, (![A_704]: (k9_relat_1('#skF_4', A_704)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_6072, c_7065])).
% 6.93/2.54  tff(c_8334, plain, (![A_870, B_871, C_872, D_873]: (k7_relset_1(A_870, B_871, C_872, D_873)=k9_relat_1(C_872, D_873) | ~m1_subset_1(C_872, k1_zfmisc_1(k2_zfmisc_1(A_870, B_871))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.93/2.54  tff(c_8348, plain, (![D_873]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_873)=k9_relat_1('#skF_4', D_873))), inference(resolution, [status(thm)], [c_84, c_8334])).
% 6.93/2.54  tff(c_8359, plain, (![D_873]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_873)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_7071, c_8348])).
% 6.93/2.54  tff(c_8372, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8359, c_80])).
% 6.93/2.54  tff(c_8375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_8372])).
% 6.93/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.93/2.54  
% 6.93/2.54  Inference rules
% 6.93/2.54  ----------------------
% 6.93/2.54  #Ref     : 0
% 6.93/2.54  #Sup     : 1791
% 6.93/2.54  #Fact    : 0
% 6.93/2.54  #Define  : 0
% 6.93/2.54  #Split   : 21
% 6.93/2.54  #Chain   : 0
% 6.93/2.54  #Close   : 0
% 6.93/2.54  
% 6.93/2.54  Ordering : KBO
% 6.93/2.54  
% 6.93/2.54  Simplification rules
% 6.93/2.54  ----------------------
% 6.93/2.54  #Subsume      : 278
% 6.93/2.54  #Demod        : 1262
% 6.93/2.54  #Tautology    : 735
% 6.93/2.54  #SimpNegUnit  : 23
% 6.93/2.54  #BackRed      : 16
% 6.93/2.54  
% 6.93/2.54  #Partial instantiations: 0
% 6.93/2.54  #Strategies tried      : 1
% 6.93/2.54  
% 6.93/2.54  Timing (in seconds)
% 6.93/2.54  ----------------------
% 6.93/2.54  Preprocessing        : 0.38
% 6.93/2.54  Parsing              : 0.21
% 6.93/2.54  CNF conversion       : 0.03
% 6.93/2.54  Main loop            : 1.34
% 6.93/2.54  Inferencing          : 0.45
% 6.93/2.54  Reduction            : 0.48
% 6.93/2.54  Demodulation         : 0.34
% 6.93/2.54  BG Simplification    : 0.05
% 6.93/2.54  Subsumption          : 0.25
% 6.93/2.54  Abstraction          : 0.05
% 6.93/2.54  MUC search           : 0.00
% 6.93/2.54  Cooper               : 0.00
% 6.93/2.54  Total                : 1.76
% 6.93/2.54  Index Insertion      : 0.00
% 6.93/2.54  Index Deletion       : 0.00
% 6.93/2.54  Index Matching       : 0.00
% 6.93/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
