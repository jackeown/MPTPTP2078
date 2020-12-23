%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:17 EST 2020

% Result     : Theorem 8.26s
% Output     : CNFRefutation 8.26s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 112 expanded)
%              Number of leaves         :   46 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  132 ( 214 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_89,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_58,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_102,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_261,plain,(
    ! [C_104,B_105,A_106] :
      ( v5_relat_1(C_104,B_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_270,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_90,c_261])).

tff(c_88,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_62,plain,(
    ! [A_33,B_34] : v1_relat_1(k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_206,plain,(
    ! [B_91,A_92] :
      ( v1_relat_1(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_212,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_90,c_206])).

tff(c_216,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_212])).

tff(c_94,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_92,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4611,plain,(
    ! [A_7780,B_7781,C_7782] :
      ( k1_relset_1(A_7780,B_7781,C_7782) = k1_relat_1(C_7782)
      | ~ m1_subset_1(C_7782,k1_zfmisc_1(k2_zfmisc_1(A_7780,B_7781))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4622,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_90,c_4611])).

tff(c_5722,plain,(
    ! [B_9727,A_9728,C_9729] :
      ( k1_xboole_0 = B_9727
      | k1_relset_1(A_9728,B_9727,C_9729) = A_9728
      | ~ v1_funct_2(C_9729,A_9728,B_9727)
      | ~ m1_subset_1(C_9729,k1_zfmisc_1(k2_zfmisc_1(A_9728,B_9727))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5731,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_90,c_5722])).

tff(c_5735,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_4622,c_5731])).

tff(c_5736,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5735])).

tff(c_60,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v5_relat_1(B_32,A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5215,plain,(
    ! [B_8851,A_8852] :
      ( r2_hidden(k1_funct_1(B_8851,A_8852),k2_relat_1(B_8851))
      | ~ r2_hidden(A_8852,k1_relat_1(B_8851))
      | ~ v1_funct_1(B_8851)
      | ~ v1_relat_1(B_8851) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_52,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_337,plain,(
    ! [A_123,C_124,B_125] :
      ( m1_subset_1(A_123,C_124)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(C_124))
      | ~ r2_hidden(A_123,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_342,plain,(
    ! [A_123,B_24,A_23] :
      ( m1_subset_1(A_123,B_24)
      | ~ r2_hidden(A_123,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_52,c_337])).

tff(c_8188,plain,(
    ! [B_12446,A_12447,B_12448] :
      ( m1_subset_1(k1_funct_1(B_12446,A_12447),B_12448)
      | ~ r1_tarski(k2_relat_1(B_12446),B_12448)
      | ~ r2_hidden(A_12447,k1_relat_1(B_12446))
      | ~ v1_funct_1(B_12446)
      | ~ v1_relat_1(B_12446) ) ),
    inference(resolution,[status(thm)],[c_5215,c_342])).

tff(c_8193,plain,(
    ! [B_12481,A_12482,A_12483] :
      ( m1_subset_1(k1_funct_1(B_12481,A_12482),A_12483)
      | ~ r2_hidden(A_12482,k1_relat_1(B_12481))
      | ~ v1_funct_1(B_12481)
      | ~ v5_relat_1(B_12481,A_12483)
      | ~ v1_relat_1(B_12481) ) ),
    inference(resolution,[status(thm)],[c_60,c_8188])).

tff(c_8204,plain,(
    ! [A_12482,A_12483] :
      ( m1_subset_1(k1_funct_1('#skF_8',A_12482),A_12483)
      | ~ r2_hidden(A_12482,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_12483)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5736,c_8193])).

tff(c_8454,plain,(
    ! [A_12550,A_12551] :
      ( m1_subset_1(k1_funct_1('#skF_8',A_12550),A_12551)
      | ~ r2_hidden(A_12550,'#skF_5')
      | ~ v5_relat_1('#skF_8',A_12551) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_94,c_8204])).

tff(c_46,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_tarski(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_228,plain,(
    ! [A_95,B_96] :
      ( r2_hidden(A_95,B_96)
      | v1_xboole_0(B_96)
      | ~ m1_subset_1(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_232,plain,(
    ! [A_95,A_9] :
      ( A_95 = A_9
      | v1_xboole_0(k1_tarski(A_9))
      | ~ m1_subset_1(A_95,k1_tarski(A_9)) ) ),
    inference(resolution,[status(thm)],[c_228,c_28])).

tff(c_238,plain,(
    ! [A_95,A_9] :
      ( A_95 = A_9
      | ~ m1_subset_1(A_95,k1_tarski(A_9)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_232])).

tff(c_8592,plain,(
    ! [A_12650,A_12651] :
      ( k1_funct_1('#skF_8',A_12650) = A_12651
      | ~ r2_hidden(A_12650,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_12651)) ) ),
    inference(resolution,[status(thm)],[c_8454,c_238])).

tff(c_8621,plain,(
    ! [A_12684] :
      ( k1_funct_1('#skF_8','#skF_7') = A_12684
      | ~ v5_relat_1('#skF_8',k1_tarski(A_12684)) ) ),
    inference(resolution,[status(thm)],[c_88,c_8592])).

tff(c_8628,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_270,c_8621])).

tff(c_8632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_8628])).

tff(c_8633,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5735])).

tff(c_30,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_109,plain,(
    ! [B_57,A_58] :
      ( ~ r1_tarski(B_57,A_58)
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_120,plain,(
    ! [C_13] : ~ r1_tarski(k1_tarski(C_13),C_13) ),
    inference(resolution,[status(thm)],[c_30,c_109])).

tff(c_8662,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_8633,c_120])).

tff(c_8721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.26/2.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.26/2.80  
% 8.26/2.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.26/2.80  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 8.26/2.80  
% 8.26/2.80  %Foreground sorts:
% 8.26/2.80  
% 8.26/2.80  
% 8.26/2.80  %Background operators:
% 8.26/2.80  
% 8.26/2.80  
% 8.26/2.80  %Foreground operators:
% 8.26/2.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.26/2.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.26/2.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.26/2.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.26/2.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.26/2.80  tff('#skF_7', type, '#skF_7': $i).
% 8.26/2.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.26/2.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.26/2.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.26/2.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.26/2.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.26/2.80  tff('#skF_5', type, '#skF_5': $i).
% 8.26/2.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.26/2.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.26/2.80  tff('#skF_6', type, '#skF_6': $i).
% 8.26/2.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.26/2.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.26/2.80  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.26/2.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.26/2.80  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.26/2.80  tff('#skF_8', type, '#skF_8': $i).
% 8.26/2.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.26/2.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.26/2.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.26/2.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.26/2.80  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.26/2.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 8.26/2.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.26/2.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.26/2.80  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.26/2.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.26/2.80  
% 8.26/2.82  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.26/2.82  tff(f_141, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 8.26/2.82  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.26/2.82  tff(f_89, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.26/2.82  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.26/2.82  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.26/2.82  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 8.26/2.82  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.26/2.82  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 8.26/2.82  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.26/2.82  tff(f_74, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 8.26/2.82  tff(f_58, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 8.26/2.82  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 8.26/2.82  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 8.26/2.82  tff(f_102, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.26/2.82  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.26/2.82  tff(c_86, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.26/2.82  tff(c_90, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.26/2.82  tff(c_261, plain, (![C_104, B_105, A_106]: (v5_relat_1(C_104, B_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.26/2.82  tff(c_270, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_90, c_261])).
% 8.26/2.82  tff(c_88, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.26/2.82  tff(c_62, plain, (![A_33, B_34]: (v1_relat_1(k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.26/2.82  tff(c_206, plain, (![B_91, A_92]: (v1_relat_1(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.26/2.82  tff(c_212, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_90, c_206])).
% 8.26/2.82  tff(c_216, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_212])).
% 8.26/2.82  tff(c_94, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.26/2.82  tff(c_92, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.26/2.82  tff(c_4611, plain, (![A_7780, B_7781, C_7782]: (k1_relset_1(A_7780, B_7781, C_7782)=k1_relat_1(C_7782) | ~m1_subset_1(C_7782, k1_zfmisc_1(k2_zfmisc_1(A_7780, B_7781))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.26/2.82  tff(c_4622, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_90, c_4611])).
% 8.26/2.82  tff(c_5722, plain, (![B_9727, A_9728, C_9729]: (k1_xboole_0=B_9727 | k1_relset_1(A_9728, B_9727, C_9729)=A_9728 | ~v1_funct_2(C_9729, A_9728, B_9727) | ~m1_subset_1(C_9729, k1_zfmisc_1(k2_zfmisc_1(A_9728, B_9727))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.26/2.82  tff(c_5731, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_90, c_5722])).
% 8.26/2.82  tff(c_5735, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_4622, c_5731])).
% 8.26/2.82  tff(c_5736, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_5735])).
% 8.26/2.82  tff(c_60, plain, (![B_32, A_31]: (r1_tarski(k2_relat_1(B_32), A_31) | ~v5_relat_1(B_32, A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.26/2.82  tff(c_5215, plain, (![B_8851, A_8852]: (r2_hidden(k1_funct_1(B_8851, A_8852), k2_relat_1(B_8851)) | ~r2_hidden(A_8852, k1_relat_1(B_8851)) | ~v1_funct_1(B_8851) | ~v1_relat_1(B_8851))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.26/2.82  tff(c_52, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.26/2.82  tff(c_337, plain, (![A_123, C_124, B_125]: (m1_subset_1(A_123, C_124) | ~m1_subset_1(B_125, k1_zfmisc_1(C_124)) | ~r2_hidden(A_123, B_125))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.26/2.82  tff(c_342, plain, (![A_123, B_24, A_23]: (m1_subset_1(A_123, B_24) | ~r2_hidden(A_123, A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_52, c_337])).
% 8.26/2.82  tff(c_8188, plain, (![B_12446, A_12447, B_12448]: (m1_subset_1(k1_funct_1(B_12446, A_12447), B_12448) | ~r1_tarski(k2_relat_1(B_12446), B_12448) | ~r2_hidden(A_12447, k1_relat_1(B_12446)) | ~v1_funct_1(B_12446) | ~v1_relat_1(B_12446))), inference(resolution, [status(thm)], [c_5215, c_342])).
% 8.26/2.82  tff(c_8193, plain, (![B_12481, A_12482, A_12483]: (m1_subset_1(k1_funct_1(B_12481, A_12482), A_12483) | ~r2_hidden(A_12482, k1_relat_1(B_12481)) | ~v1_funct_1(B_12481) | ~v5_relat_1(B_12481, A_12483) | ~v1_relat_1(B_12481))), inference(resolution, [status(thm)], [c_60, c_8188])).
% 8.26/2.82  tff(c_8204, plain, (![A_12482, A_12483]: (m1_subset_1(k1_funct_1('#skF_8', A_12482), A_12483) | ~r2_hidden(A_12482, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_12483) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5736, c_8193])).
% 8.26/2.82  tff(c_8454, plain, (![A_12550, A_12551]: (m1_subset_1(k1_funct_1('#skF_8', A_12550), A_12551) | ~r2_hidden(A_12550, '#skF_5') | ~v5_relat_1('#skF_8', A_12551))), inference(demodulation, [status(thm), theory('equality')], [c_216, c_94, c_8204])).
% 8.26/2.82  tff(c_46, plain, (![A_20]: (~v1_xboole_0(k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.26/2.82  tff(c_228, plain, (![A_95, B_96]: (r2_hidden(A_95, B_96) | v1_xboole_0(B_96) | ~m1_subset_1(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.26/2.82  tff(c_28, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.26/2.82  tff(c_232, plain, (![A_95, A_9]: (A_95=A_9 | v1_xboole_0(k1_tarski(A_9)) | ~m1_subset_1(A_95, k1_tarski(A_9)))), inference(resolution, [status(thm)], [c_228, c_28])).
% 8.26/2.82  tff(c_238, plain, (![A_95, A_9]: (A_95=A_9 | ~m1_subset_1(A_95, k1_tarski(A_9)))), inference(negUnitSimplification, [status(thm)], [c_46, c_232])).
% 8.26/2.82  tff(c_8592, plain, (![A_12650, A_12651]: (k1_funct_1('#skF_8', A_12650)=A_12651 | ~r2_hidden(A_12650, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_12651)))), inference(resolution, [status(thm)], [c_8454, c_238])).
% 8.26/2.82  tff(c_8621, plain, (![A_12684]: (k1_funct_1('#skF_8', '#skF_7')=A_12684 | ~v5_relat_1('#skF_8', k1_tarski(A_12684)))), inference(resolution, [status(thm)], [c_88, c_8592])).
% 8.26/2.82  tff(c_8628, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_270, c_8621])).
% 8.26/2.82  tff(c_8632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_8628])).
% 8.26/2.82  tff(c_8633, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_5735])).
% 8.26/2.82  tff(c_30, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.26/2.82  tff(c_109, plain, (![B_57, A_58]: (~r1_tarski(B_57, A_58) | ~r2_hidden(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.26/2.82  tff(c_120, plain, (![C_13]: (~r1_tarski(k1_tarski(C_13), C_13))), inference(resolution, [status(thm)], [c_30, c_109])).
% 8.26/2.82  tff(c_8662, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_8633, c_120])).
% 8.26/2.82  tff(c_8721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_8662])).
% 8.26/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.26/2.82  
% 8.26/2.82  Inference rules
% 8.26/2.82  ----------------------
% 8.26/2.82  #Ref     : 0
% 8.26/2.82  #Sup     : 1259
% 8.26/2.82  #Fact    : 2
% 8.26/2.82  #Define  : 0
% 8.26/2.82  #Split   : 51
% 8.26/2.82  #Chain   : 0
% 8.26/2.82  #Close   : 0
% 8.26/2.82  
% 8.26/2.82  Ordering : KBO
% 8.26/2.82  
% 8.26/2.82  Simplification rules
% 8.26/2.82  ----------------------
% 8.26/2.82  #Subsume      : 307
% 8.26/2.82  #Demod        : 286
% 8.26/2.82  #Tautology    : 379
% 8.26/2.82  #SimpNegUnit  : 99
% 8.26/2.82  #BackRed      : 75
% 8.26/2.82  
% 8.26/2.82  #Partial instantiations: 7125
% 8.26/2.82  #Strategies tried      : 1
% 8.26/2.82  
% 8.26/2.82  Timing (in seconds)
% 8.26/2.82  ----------------------
% 8.26/2.82  Preprocessing        : 0.35
% 8.26/2.82  Parsing              : 0.18
% 8.26/2.82  CNF conversion       : 0.03
% 8.26/2.82  Main loop            : 1.70
% 8.26/2.82  Inferencing          : 0.72
% 8.26/2.82  Reduction            : 0.46
% 8.26/2.82  Demodulation         : 0.31
% 8.26/2.82  BG Simplification    : 0.06
% 8.26/2.82  Subsumption          : 0.33
% 8.26/2.82  Abstraction          : 0.07
% 8.26/2.82  MUC search           : 0.00
% 8.26/2.82  Cooper               : 0.00
% 8.26/2.82  Total                : 2.08
% 8.26/2.82  Index Insertion      : 0.00
% 8.26/2.82  Index Deletion       : 0.00
% 8.26/2.82  Index Matching       : 0.00
% 8.26/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
