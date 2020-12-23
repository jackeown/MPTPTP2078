%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:17 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 101 expanded)
%              Number of leaves         :   41 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 187 expanded)
%              Number of equality atoms :   31 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_62,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_56,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_48,plain,(
    ! [A_20] : k2_zfmisc_1(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_123,plain,(
    ! [A_49,B_50] : ~ r2_hidden(A_49,k2_zfmisc_1(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_126,plain,(
    ! [A_20] : ~ r2_hidden(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_123])).

tff(c_80,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_84,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_217,plain,(
    ! [C_79,B_80,A_81] :
      ( v5_relat_1(C_79,B_80)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_227,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_217])).

tff(c_82,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_58,plain,(
    ! [A_29,B_30] : v1_relat_1(k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_196,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_199,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_84,c_196])).

tff(c_202,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_199])).

tff(c_88,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_86,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_642,plain,(
    ! [A_1617,B_1618,C_1619] :
      ( k1_relset_1(A_1617,B_1618,C_1619) = k1_relat_1(C_1619)
      | ~ m1_subset_1(C_1619,k1_zfmisc_1(k2_zfmisc_1(A_1617,B_1618))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_654,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_642])).

tff(c_1354,plain,(
    ! [B_2375,A_2376,C_2377] :
      ( k1_xboole_0 = B_2375
      | k1_relset_1(A_2376,B_2375,C_2377) = A_2376
      | ~ v1_funct_2(C_2377,A_2376,B_2375)
      | ~ m1_subset_1(C_2377,k1_zfmisc_1(k2_zfmisc_1(A_2376,B_2375))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1359,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_1354])).

tff(c_1368,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_654,c_1359])).

tff(c_1370,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1368])).

tff(c_60,plain,(
    ! [C_33,B_32,A_31] :
      ( m1_subset_1(k1_funct_1(C_33,B_32),A_31)
      | ~ r2_hidden(B_32,k1_relat_1(C_33))
      | ~ v1_funct_1(C_33)
      | ~ v5_relat_1(C_33,A_31)
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1374,plain,(
    ! [B_32,A_31] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_32),A_31)
      | ~ r2_hidden(B_32,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_31)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1370,c_60])).

tff(c_1431,plain,(
    ! [B_2471,A_2472] :
      ( m1_subset_1(k1_funct_1('#skF_8',B_2471),A_2472)
      | ~ r2_hidden(B_2471,'#skF_5')
      | ~ v5_relat_1('#skF_8',A_2472) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_88,c_1374])).

tff(c_44,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_tarski(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_178,plain,(
    ! [A_70,B_71] :
      ( r2_hidden(A_70,B_71)
      | v1_xboole_0(B_71)
      | ~ m1_subset_1(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_182,plain,(
    ! [A_8,A_70] :
      ( A_8 = A_70
      | v1_xboole_0(k1_tarski(A_8))
      | ~ m1_subset_1(A_70,k1_tarski(A_8)) ) ),
    inference(resolution,[status(thm)],[c_178,c_26])).

tff(c_193,plain,(
    ! [A_8,A_70] :
      ( A_8 = A_70
      | ~ m1_subset_1(A_70,k1_tarski(A_8)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_182])).

tff(c_1502,plain,(
    ! [B_2535,A_2536] :
      ( k1_funct_1('#skF_8',B_2535) = A_2536
      | ~ r2_hidden(B_2535,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2536)) ) ),
    inference(resolution,[status(thm)],[c_1431,c_193])).

tff(c_1517,plain,(
    ! [A_2568] :
      ( k1_funct_1('#skF_8','#skF_7') = A_2568
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2568)) ) ),
    inference(resolution,[status(thm)],[c_82,c_1502])).

tff(c_1524,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_227,c_1517])).

tff(c_1528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1524])).

tff(c_1529,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1368])).

tff(c_28,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1569,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1529,c_28])).

tff(c_1622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_1569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n024.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 17:46:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.53  
% 3.37/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.54  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 3.37/1.54  
% 3.37/1.54  %Foreground sorts:
% 3.37/1.54  
% 3.37/1.54  
% 3.37/1.54  %Background operators:
% 3.37/1.54  
% 3.37/1.54  
% 3.37/1.54  %Foreground operators:
% 3.37/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.37/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.37/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.37/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.37/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.37/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.37/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.37/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.37/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.37/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.37/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.37/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.37/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.37/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.37/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.37/1.54  tff('#skF_8', type, '#skF_8': $i).
% 3.37/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.37/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.37/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.37/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.37/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.37/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.37/1.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.37/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.37/1.54  
% 3.51/1.55  tff(f_62, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.51/1.55  tff(f_65, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.51/1.55  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.51/1.55  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.51/1.55  tff(f_80, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.51/1.55  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.51/1.55  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.51/1.55  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.51/1.55  tff(f_90, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 3.51/1.55  tff(f_56, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.51/1.55  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.51/1.55  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.51/1.55  tff(c_48, plain, (![A_20]: (k2_zfmisc_1(A_20, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.51/1.55  tff(c_123, plain, (![A_49, B_50]: (~r2_hidden(A_49, k2_zfmisc_1(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.51/1.55  tff(c_126, plain, (![A_20]: (~r2_hidden(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_48, c_123])).
% 3.51/1.55  tff(c_80, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.51/1.55  tff(c_84, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.51/1.55  tff(c_217, plain, (![C_79, B_80, A_81]: (v5_relat_1(C_79, B_80) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.51/1.55  tff(c_227, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_217])).
% 3.51/1.55  tff(c_82, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.51/1.55  tff(c_58, plain, (![A_29, B_30]: (v1_relat_1(k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.51/1.55  tff(c_196, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.51/1.55  tff(c_199, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_84, c_196])).
% 3.51/1.55  tff(c_202, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_199])).
% 3.51/1.55  tff(c_88, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.51/1.55  tff(c_86, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.51/1.55  tff(c_642, plain, (![A_1617, B_1618, C_1619]: (k1_relset_1(A_1617, B_1618, C_1619)=k1_relat_1(C_1619) | ~m1_subset_1(C_1619, k1_zfmisc_1(k2_zfmisc_1(A_1617, B_1618))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.51/1.55  tff(c_654, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_84, c_642])).
% 3.51/1.55  tff(c_1354, plain, (![B_2375, A_2376, C_2377]: (k1_xboole_0=B_2375 | k1_relset_1(A_2376, B_2375, C_2377)=A_2376 | ~v1_funct_2(C_2377, A_2376, B_2375) | ~m1_subset_1(C_2377, k1_zfmisc_1(k2_zfmisc_1(A_2376, B_2375))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.51/1.55  tff(c_1359, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_1354])).
% 3.51/1.55  tff(c_1368, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_654, c_1359])).
% 3.51/1.55  tff(c_1370, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_1368])).
% 3.51/1.55  tff(c_60, plain, (![C_33, B_32, A_31]: (m1_subset_1(k1_funct_1(C_33, B_32), A_31) | ~r2_hidden(B_32, k1_relat_1(C_33)) | ~v1_funct_1(C_33) | ~v5_relat_1(C_33, A_31) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.51/1.55  tff(c_1374, plain, (![B_32, A_31]: (m1_subset_1(k1_funct_1('#skF_8', B_32), A_31) | ~r2_hidden(B_32, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_31) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1370, c_60])).
% 3.51/1.55  tff(c_1431, plain, (![B_2471, A_2472]: (m1_subset_1(k1_funct_1('#skF_8', B_2471), A_2472) | ~r2_hidden(B_2471, '#skF_5') | ~v5_relat_1('#skF_8', A_2472))), inference(demodulation, [status(thm), theory('equality')], [c_202, c_88, c_1374])).
% 3.51/1.55  tff(c_44, plain, (![A_19]: (~v1_xboole_0(k1_tarski(A_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.51/1.55  tff(c_178, plain, (![A_70, B_71]: (r2_hidden(A_70, B_71) | v1_xboole_0(B_71) | ~m1_subset_1(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.51/1.55  tff(c_26, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.51/1.55  tff(c_182, plain, (![A_8, A_70]: (A_8=A_70 | v1_xboole_0(k1_tarski(A_8)) | ~m1_subset_1(A_70, k1_tarski(A_8)))), inference(resolution, [status(thm)], [c_178, c_26])).
% 3.51/1.55  tff(c_193, plain, (![A_8, A_70]: (A_8=A_70 | ~m1_subset_1(A_70, k1_tarski(A_8)))), inference(negUnitSimplification, [status(thm)], [c_44, c_182])).
% 3.51/1.55  tff(c_1502, plain, (![B_2535, A_2536]: (k1_funct_1('#skF_8', B_2535)=A_2536 | ~r2_hidden(B_2535, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_2536)))), inference(resolution, [status(thm)], [c_1431, c_193])).
% 3.51/1.55  tff(c_1517, plain, (![A_2568]: (k1_funct_1('#skF_8', '#skF_7')=A_2568 | ~v5_relat_1('#skF_8', k1_tarski(A_2568)))), inference(resolution, [status(thm)], [c_82, c_1502])).
% 3.51/1.55  tff(c_1524, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_227, c_1517])).
% 3.51/1.55  tff(c_1528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1524])).
% 3.51/1.55  tff(c_1529, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1368])).
% 3.51/1.55  tff(c_28, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.51/1.55  tff(c_1569, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1529, c_28])).
% 3.51/1.55  tff(c_1622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_1569])).
% 3.51/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.55  
% 3.51/1.55  Inference rules
% 3.51/1.55  ----------------------
% 3.51/1.55  #Ref     : 0
% 3.51/1.55  #Sup     : 229
% 3.51/1.55  #Fact    : 0
% 3.51/1.55  #Define  : 0
% 3.51/1.55  #Split   : 8
% 3.51/1.55  #Chain   : 0
% 3.51/1.55  #Close   : 0
% 3.51/1.55  
% 3.51/1.55  Ordering : KBO
% 3.51/1.55  
% 3.51/1.55  Simplification rules
% 3.51/1.55  ----------------------
% 3.51/1.55  #Subsume      : 35
% 3.51/1.55  #Demod        : 46
% 3.51/1.55  #Tautology    : 69
% 3.51/1.55  #SimpNegUnit  : 9
% 3.51/1.55  #BackRed      : 5
% 3.51/1.55  
% 3.51/1.55  #Partial instantiations: 1422
% 3.51/1.55  #Strategies tried      : 1
% 3.51/1.55  
% 3.51/1.55  Timing (in seconds)
% 3.51/1.55  ----------------------
% 3.51/1.55  Preprocessing        : 0.33
% 3.51/1.55  Parsing              : 0.17
% 3.51/1.55  CNF conversion       : 0.03
% 3.51/1.55  Main loop            : 0.45
% 3.51/1.55  Inferencing          : 0.21
% 3.51/1.55  Reduction            : 0.12
% 3.51/1.55  Demodulation         : 0.08
% 3.51/1.55  BG Simplification    : 0.03
% 3.51/1.55  Subsumption          : 0.07
% 3.51/1.55  Abstraction          : 0.02
% 3.51/1.55  MUC search           : 0.00
% 3.51/1.55  Cooper               : 0.00
% 3.51/1.55  Total                : 0.81
% 3.51/1.55  Index Insertion      : 0.00
% 3.51/1.55  Index Deletion       : 0.00
% 3.51/1.55  Index Matching       : 0.00
% 3.51/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
