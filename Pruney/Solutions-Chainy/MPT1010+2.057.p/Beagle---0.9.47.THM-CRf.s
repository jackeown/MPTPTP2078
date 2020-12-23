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
% DateTime   : Thu Dec  3 10:15:12 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 111 expanded)
%              Number of leaves         :   43 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 203 expanded)
%              Number of equality atoms :   30 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_112,axiom,(
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

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_40,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_72,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_76,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_74,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_337,plain,(
    ! [A_93,B_94,C_95] :
      ( k1_relset_1(A_93,B_94,C_95) = k1_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_341,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_337])).

tff(c_1849,plain,(
    ! [B_291,A_292,C_293] :
      ( k1_xboole_0 = B_291
      | k1_relset_1(A_292,B_291,C_293) = A_292
      | ~ v1_funct_2(C_293,A_292,B_291)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_292,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1856,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_74,c_1849])).

tff(c_1860,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_341,c_1856])).

tff(c_1861,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1860])).

tff(c_202,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_206,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_202])).

tff(c_78,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1061,plain,(
    ! [B_179,A_180] :
      ( r2_hidden(k1_funct_1(B_179,A_180),k2_relat_1(B_179))
      | ~ r2_hidden(A_180,k1_relat_1(B_179))
      | ~ v1_funct_1(B_179)
      | ~ v1_relat_1(B_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_353,plain,(
    ! [A_99,B_100,C_101] :
      ( k2_relset_1(A_99,B_100,C_101) = k2_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_357,plain,(
    k2_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_353])).

tff(c_431,plain,(
    ! [A_107,B_108,C_109] :
      ( m1_subset_1(k2_relset_1(A_107,B_108,C_109),k1_zfmisc_1(B_108))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_448,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(k1_tarski('#skF_7')))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_431])).

tff(c_454,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_448])).

tff(c_44,plain,(
    ! [A_22,C_24,B_23] :
      ( m1_subset_1(A_22,C_24)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(C_24))
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_471,plain,(
    ! [A_22] :
      ( m1_subset_1(A_22,k1_tarski('#skF_7'))
      | ~ r2_hidden(A_22,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_454,c_44])).

tff(c_1065,plain,(
    ! [A_180] :
      ( m1_subset_1(k1_funct_1('#skF_9',A_180),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_180,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1061,c_471])).

tff(c_1120,plain,(
    ! [A_183] :
      ( m1_subset_1(k1_funct_1('#skF_9',A_183),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_183,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_78,c_1065])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_95,plain,(
    ! [B_49,A_50] :
      ( ~ r2_hidden(B_49,A_50)
      | ~ v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [C_10] : ~ v1_xboole_0(k1_tarski(C_10)) ),
    inference(resolution,[status(thm)],[c_10,c_95])).

tff(c_207,plain,(
    ! [A_73,B_74] :
      ( r2_hidden(A_73,B_74)
      | v1_xboole_0(B_74)
      | ~ m1_subset_1(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_211,plain,(
    ! [A_73,A_6] :
      ( A_73 = A_6
      | v1_xboole_0(k1_tarski(A_6))
      | ~ m1_subset_1(A_73,k1_tarski(A_6)) ) ),
    inference(resolution,[status(thm)],[c_207,c_8])).

tff(c_220,plain,(
    ! [A_73,A_6] :
      ( A_73 = A_6
      | ~ m1_subset_1(A_73,k1_tarski(A_6)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_211])).

tff(c_1124,plain,(
    ! [A_183] :
      ( k1_funct_1('#skF_9',A_183) = '#skF_7'
      | ~ r2_hidden(A_183,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1120,c_220])).

tff(c_1907,plain,(
    ! [A_297] :
      ( k1_funct_1('#skF_9',A_297) = '#skF_7'
      | ~ r2_hidden(A_297,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_1124])).

tff(c_1926,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_72,c_1907])).

tff(c_1938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1926])).

tff(c_1939,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1860])).

tff(c_121,plain,(
    ! [B_56,A_57] :
      ( ~ r1_tarski(B_56,A_57)
      | ~ r2_hidden(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_136,plain,(
    ! [C_10] : ~ r1_tarski(k1_tarski(C_10),C_10) ),
    inference(resolution,[status(thm)],[c_10,c_121])).

tff(c_1982,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1939,c_136])).

tff(c_1997,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1982])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:00:49 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.99  
% 4.69/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/2.00  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2
% 4.69/2.00  
% 4.69/2.00  %Foreground sorts:
% 4.69/2.00  
% 4.69/2.00  
% 4.69/2.00  %Background operators:
% 4.69/2.00  
% 4.69/2.00  
% 4.69/2.00  %Foreground operators:
% 4.69/2.00  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.69/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.69/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.69/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.69/2.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.69/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.69/2.00  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.69/2.00  tff('#skF_7', type, '#skF_7': $i).
% 4.69/2.00  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.69/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/2.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.69/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.69/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.69/2.00  tff('#skF_6', type, '#skF_6': $i).
% 4.69/2.00  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.69/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.69/2.00  tff('#skF_9', type, '#skF_9': $i).
% 4.69/2.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.69/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.69/2.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.69/2.00  tff('#skF_8', type, '#skF_8': $i).
% 4.69/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.69/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.69/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.69/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.69/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.69/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.69/2.00  
% 4.69/2.01  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.69/2.01  tff(f_123, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 4.69/2.01  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.69/2.01  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.69/2.01  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.69/2.01  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 4.69/2.01  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.69/2.01  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.69/2.01  tff(f_65, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.69/2.01  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.69/2.01  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.69/2.01  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.69/2.01  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.69/2.01  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.69/2.01  tff(c_70, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.69/2.01  tff(c_72, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.69/2.01  tff(c_76, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.69/2.01  tff(c_74, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.69/2.01  tff(c_337, plain, (![A_93, B_94, C_95]: (k1_relset_1(A_93, B_94, C_95)=k1_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.69/2.01  tff(c_341, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_337])).
% 4.69/2.01  tff(c_1849, plain, (![B_291, A_292, C_293]: (k1_xboole_0=B_291 | k1_relset_1(A_292, B_291, C_293)=A_292 | ~v1_funct_2(C_293, A_292, B_291) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_292, B_291))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.69/2.01  tff(c_1856, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_74, c_1849])).
% 4.69/2.01  tff(c_1860, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_341, c_1856])).
% 4.69/2.01  tff(c_1861, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_1860])).
% 4.69/2.01  tff(c_202, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.69/2.01  tff(c_206, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_202])).
% 4.69/2.01  tff(c_78, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.69/2.01  tff(c_1061, plain, (![B_179, A_180]: (r2_hidden(k1_funct_1(B_179, A_180), k2_relat_1(B_179)) | ~r2_hidden(A_180, k1_relat_1(B_179)) | ~v1_funct_1(B_179) | ~v1_relat_1(B_179))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.69/2.01  tff(c_353, plain, (![A_99, B_100, C_101]: (k2_relset_1(A_99, B_100, C_101)=k2_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.69/2.01  tff(c_357, plain, (k2_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_74, c_353])).
% 4.69/2.01  tff(c_431, plain, (![A_107, B_108, C_109]: (m1_subset_1(k2_relset_1(A_107, B_108, C_109), k1_zfmisc_1(B_108)) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.69/2.01  tff(c_448, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(k1_tarski('#skF_7'))) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_357, c_431])).
% 4.69/2.01  tff(c_454, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_448])).
% 4.69/2.01  tff(c_44, plain, (![A_22, C_24, B_23]: (m1_subset_1(A_22, C_24) | ~m1_subset_1(B_23, k1_zfmisc_1(C_24)) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.69/2.01  tff(c_471, plain, (![A_22]: (m1_subset_1(A_22, k1_tarski('#skF_7')) | ~r2_hidden(A_22, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_454, c_44])).
% 4.69/2.01  tff(c_1065, plain, (![A_180]: (m1_subset_1(k1_funct_1('#skF_9', A_180), k1_tarski('#skF_7')) | ~r2_hidden(A_180, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1061, c_471])).
% 4.69/2.01  tff(c_1120, plain, (![A_183]: (m1_subset_1(k1_funct_1('#skF_9', A_183), k1_tarski('#skF_7')) | ~r2_hidden(A_183, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_78, c_1065])).
% 4.69/2.01  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.69/2.01  tff(c_95, plain, (![B_49, A_50]: (~r2_hidden(B_49, A_50) | ~v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/2.01  tff(c_106, plain, (![C_10]: (~v1_xboole_0(k1_tarski(C_10)))), inference(resolution, [status(thm)], [c_10, c_95])).
% 4.69/2.01  tff(c_207, plain, (![A_73, B_74]: (r2_hidden(A_73, B_74) | v1_xboole_0(B_74) | ~m1_subset_1(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/2.01  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.69/2.01  tff(c_211, plain, (![A_73, A_6]: (A_73=A_6 | v1_xboole_0(k1_tarski(A_6)) | ~m1_subset_1(A_73, k1_tarski(A_6)))), inference(resolution, [status(thm)], [c_207, c_8])).
% 4.69/2.01  tff(c_220, plain, (![A_73, A_6]: (A_73=A_6 | ~m1_subset_1(A_73, k1_tarski(A_6)))), inference(negUnitSimplification, [status(thm)], [c_106, c_211])).
% 4.69/2.01  tff(c_1124, plain, (![A_183]: (k1_funct_1('#skF_9', A_183)='#skF_7' | ~r2_hidden(A_183, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_1120, c_220])).
% 4.69/2.01  tff(c_1907, plain, (![A_297]: (k1_funct_1('#skF_9', A_297)='#skF_7' | ~r2_hidden(A_297, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1861, c_1124])).
% 4.69/2.01  tff(c_1926, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_72, c_1907])).
% 4.69/2.01  tff(c_1938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1926])).
% 4.69/2.01  tff(c_1939, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1860])).
% 4.69/2.01  tff(c_121, plain, (![B_56, A_57]: (~r1_tarski(B_56, A_57) | ~r2_hidden(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.69/2.01  tff(c_136, plain, (![C_10]: (~r1_tarski(k1_tarski(C_10), C_10))), inference(resolution, [status(thm)], [c_10, c_121])).
% 4.69/2.01  tff(c_1982, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1939, c_136])).
% 4.69/2.01  tff(c_1997, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1982])).
% 4.69/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/2.01  
% 4.69/2.01  Inference rules
% 4.69/2.01  ----------------------
% 4.69/2.01  #Ref     : 0
% 4.69/2.01  #Sup     : 386
% 4.69/2.01  #Fact    : 2
% 4.69/2.01  #Define  : 0
% 4.69/2.01  #Split   : 10
% 4.69/2.01  #Chain   : 0
% 4.69/2.01  #Close   : 0
% 4.69/2.01  
% 4.69/2.01  Ordering : KBO
% 4.69/2.01  
% 4.69/2.01  Simplification rules
% 4.69/2.01  ----------------------
% 4.69/2.01  #Subsume      : 58
% 4.69/2.01  #Demod        : 279
% 4.69/2.01  #Tautology    : 162
% 4.69/2.01  #SimpNegUnit  : 31
% 4.69/2.01  #BackRed      : 57
% 4.69/2.01  
% 4.69/2.01  #Partial instantiations: 0
% 4.69/2.01  #Strategies tried      : 1
% 4.69/2.01  
% 4.69/2.01  Timing (in seconds)
% 4.69/2.01  ----------------------
% 4.69/2.02  Preprocessing        : 0.45
% 4.69/2.02  Parsing              : 0.24
% 4.69/2.02  CNF conversion       : 0.03
% 4.69/2.02  Main loop            : 0.76
% 4.69/2.02  Inferencing          : 0.27
% 4.69/2.02  Reduction            : 0.24
% 4.69/2.02  Demodulation         : 0.16
% 4.69/2.02  BG Simplification    : 0.04
% 4.69/2.02  Subsumption          : 0.15
% 4.69/2.02  Abstraction          : 0.04
% 4.69/2.02  MUC search           : 0.00
% 4.69/2.02  Cooper               : 0.00
% 4.69/2.02  Total                : 1.26
% 4.69/2.02  Index Insertion      : 0.00
% 4.69/2.02  Index Deletion       : 0.00
% 4.69/2.02  Index Matching       : 0.00
% 4.69/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
