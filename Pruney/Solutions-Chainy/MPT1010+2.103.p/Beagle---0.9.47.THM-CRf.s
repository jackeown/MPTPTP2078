%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:19 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 114 expanded)
%              Number of leaves         :   44 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 209 expanded)
%              Number of equality atoms :   30 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_80,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_84,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_82,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_548,plain,(
    ! [A_132,B_133,C_134] :
      ( k1_relset_1(A_132,B_133,C_134) = k1_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_552,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_548])).

tff(c_1624,plain,(
    ! [B_248,A_249,C_250] :
      ( k1_xboole_0 = B_248
      | k1_relset_1(A_249,B_248,C_250) = A_249
      | ~ v1_funct_2(C_250,A_249,B_248)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1631,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_82,c_1624])).

tff(c_1635,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_552,c_1631])).

tff(c_1636,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1635])).

tff(c_54,plain,(
    ! [A_29,B_30] : v1_relat_1(k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_269,plain,(
    ! [B_97,A_98] :
      ( v1_relat_1(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_98))
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_272,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_82,c_269])).

tff(c_275,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_272])).

tff(c_86,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1188,plain,(
    ! [B_200,A_201] :
      ( r2_hidden(k1_funct_1(B_200,A_201),k2_relat_1(B_200))
      | ~ r2_hidden(A_201,k1_relat_1(B_200))
      | ~ v1_funct_1(B_200)
      | ~ v1_relat_1(B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_553,plain,(
    ! [A_135,B_136,C_137] :
      ( k2_relset_1(A_135,B_136,C_137) = k2_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_557,plain,(
    k2_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_82,c_553])).

tff(c_570,plain,(
    ! [A_142,B_143,C_144] :
      ( m1_subset_1(k2_relset_1(A_142,B_143,C_144),k1_zfmisc_1(B_143))
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_586,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(k1_tarski('#skF_7')))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_570])).

tff(c_592,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_586])).

tff(c_50,plain,(
    ! [A_23,C_25,B_24] :
      ( m1_subset_1(A_23,C_25)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(C_25))
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_598,plain,(
    ! [A_23] :
      ( m1_subset_1(A_23,k1_tarski('#skF_7'))
      | ~ r2_hidden(A_23,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_592,c_50])).

tff(c_1192,plain,(
    ! [A_201] :
      ( m1_subset_1(k1_funct_1('#skF_9',A_201),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_201,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1188,c_598])).

tff(c_1229,plain,(
    ! [A_203] :
      ( m1_subset_1(k1_funct_1('#skF_9',A_203),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_203,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_86,c_1192])).

tff(c_34,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_99,plain,(
    ! [B_52,A_53] :
      ( ~ r2_hidden(B_52,A_53)
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [C_17] : ~ v1_xboole_0(k1_tarski(C_17)) ),
    inference(resolution,[status(thm)],[c_34,c_99])).

tff(c_244,plain,(
    ! [A_91,B_92] :
      ( r2_hidden(A_91,B_92)
      | v1_xboole_0(B_92)
      | ~ m1_subset_1(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_251,plain,(
    ! [A_91,A_13] :
      ( A_91 = A_13
      | v1_xboole_0(k1_tarski(A_13))
      | ~ m1_subset_1(A_91,k1_tarski(A_13)) ) ),
    inference(resolution,[status(thm)],[c_244,c_32])).

tff(c_258,plain,(
    ! [A_91,A_13] :
      ( A_91 = A_13
      | ~ m1_subset_1(A_91,k1_tarski(A_13)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_251])).

tff(c_1233,plain,(
    ! [A_203] :
      ( k1_funct_1('#skF_9',A_203) = '#skF_7'
      | ~ r2_hidden(A_203,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1229,c_258])).

tff(c_1670,plain,(
    ! [A_251] :
      ( k1_funct_1('#skF_9',A_251) = '#skF_7'
      | ~ r2_hidden(A_251,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1636,c_1233])).

tff(c_1689,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_80,c_1670])).

tff(c_1701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1689])).

tff(c_1702,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1635])).

tff(c_157,plain,(
    ! [B_71,A_72] :
      ( ~ r1_tarski(B_71,A_72)
      | ~ r2_hidden(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_180,plain,(
    ! [C_17] : ~ r1_tarski(k1_tarski(C_17),C_17) ),
    inference(resolution,[status(thm)],[c_34,c_157])).

tff(c_1728,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1702,c_180])).

tff(c_1745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1728])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:34:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.86/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.73  
% 3.86/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.73  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.86/1.73  
% 3.86/1.73  %Foreground sorts:
% 3.86/1.73  
% 3.86/1.73  
% 3.86/1.73  %Background operators:
% 3.86/1.73  
% 3.86/1.73  
% 3.86/1.73  %Foreground operators:
% 3.86/1.73  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.86/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.86/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.86/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.86/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.86/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.86/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.86/1.73  tff('#skF_7', type, '#skF_7': $i).
% 3.86/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.86/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.86/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.86/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.86/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.86/1.73  tff('#skF_6', type, '#skF_6': $i).
% 3.86/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.86/1.73  tff('#skF_9', type, '#skF_9': $i).
% 3.86/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.86/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.86/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.86/1.73  tff('#skF_8', type, '#skF_8': $i).
% 3.86/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.86/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.86/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.86/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.86/1.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.86/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.86/1.73  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.86/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.86/1.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.86/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.86/1.73  
% 3.86/1.75  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.86/1.75  tff(f_134, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.86/1.75  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.86/1.75  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.86/1.75  tff(f_80, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.86/1.75  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.86/1.75  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.86/1.75  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.86/1.75  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.86/1.75  tff(f_71, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.86/1.75  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.86/1.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.86/1.75  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.86/1.75  tff(f_93, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.86/1.75  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.86/1.75  tff(c_78, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.86/1.75  tff(c_80, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.86/1.75  tff(c_84, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.86/1.75  tff(c_82, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.86/1.75  tff(c_548, plain, (![A_132, B_133, C_134]: (k1_relset_1(A_132, B_133, C_134)=k1_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.86/1.75  tff(c_552, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_82, c_548])).
% 3.86/1.75  tff(c_1624, plain, (![B_248, A_249, C_250]: (k1_xboole_0=B_248 | k1_relset_1(A_249, B_248, C_250)=A_249 | ~v1_funct_2(C_250, A_249, B_248) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.86/1.75  tff(c_1631, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_82, c_1624])).
% 3.86/1.75  tff(c_1635, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_552, c_1631])).
% 3.86/1.75  tff(c_1636, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_1635])).
% 3.86/1.75  tff(c_54, plain, (![A_29, B_30]: (v1_relat_1(k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.86/1.75  tff(c_269, plain, (![B_97, A_98]: (v1_relat_1(B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_98)) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.86/1.75  tff(c_272, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_82, c_269])).
% 3.86/1.75  tff(c_275, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_272])).
% 3.86/1.75  tff(c_86, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.86/1.75  tff(c_1188, plain, (![B_200, A_201]: (r2_hidden(k1_funct_1(B_200, A_201), k2_relat_1(B_200)) | ~r2_hidden(A_201, k1_relat_1(B_200)) | ~v1_funct_1(B_200) | ~v1_relat_1(B_200))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.86/1.75  tff(c_553, plain, (![A_135, B_136, C_137]: (k2_relset_1(A_135, B_136, C_137)=k2_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.86/1.75  tff(c_557, plain, (k2_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_82, c_553])).
% 3.86/1.75  tff(c_570, plain, (![A_142, B_143, C_144]: (m1_subset_1(k2_relset_1(A_142, B_143, C_144), k1_zfmisc_1(B_143)) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_142, B_143))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.86/1.75  tff(c_586, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(k1_tarski('#skF_7'))) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_557, c_570])).
% 3.86/1.75  tff(c_592, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_586])).
% 3.86/1.75  tff(c_50, plain, (![A_23, C_25, B_24]: (m1_subset_1(A_23, C_25) | ~m1_subset_1(B_24, k1_zfmisc_1(C_25)) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.86/1.75  tff(c_598, plain, (![A_23]: (m1_subset_1(A_23, k1_tarski('#skF_7')) | ~r2_hidden(A_23, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_592, c_50])).
% 3.86/1.75  tff(c_1192, plain, (![A_201]: (m1_subset_1(k1_funct_1('#skF_9', A_201), k1_tarski('#skF_7')) | ~r2_hidden(A_201, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1188, c_598])).
% 3.86/1.75  tff(c_1229, plain, (![A_203]: (m1_subset_1(k1_funct_1('#skF_9', A_203), k1_tarski('#skF_7')) | ~r2_hidden(A_203, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_86, c_1192])).
% 3.86/1.75  tff(c_34, plain, (![C_17]: (r2_hidden(C_17, k1_tarski(C_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.86/1.75  tff(c_99, plain, (![B_52, A_53]: (~r2_hidden(B_52, A_53) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.86/1.75  tff(c_106, plain, (![C_17]: (~v1_xboole_0(k1_tarski(C_17)))), inference(resolution, [status(thm)], [c_34, c_99])).
% 3.86/1.75  tff(c_244, plain, (![A_91, B_92]: (r2_hidden(A_91, B_92) | v1_xboole_0(B_92) | ~m1_subset_1(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.86/1.75  tff(c_32, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.86/1.75  tff(c_251, plain, (![A_91, A_13]: (A_91=A_13 | v1_xboole_0(k1_tarski(A_13)) | ~m1_subset_1(A_91, k1_tarski(A_13)))), inference(resolution, [status(thm)], [c_244, c_32])).
% 3.86/1.75  tff(c_258, plain, (![A_91, A_13]: (A_91=A_13 | ~m1_subset_1(A_91, k1_tarski(A_13)))), inference(negUnitSimplification, [status(thm)], [c_106, c_251])).
% 3.86/1.75  tff(c_1233, plain, (![A_203]: (k1_funct_1('#skF_9', A_203)='#skF_7' | ~r2_hidden(A_203, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_1229, c_258])).
% 3.86/1.75  tff(c_1670, plain, (![A_251]: (k1_funct_1('#skF_9', A_251)='#skF_7' | ~r2_hidden(A_251, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1636, c_1233])).
% 3.86/1.75  tff(c_1689, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_80, c_1670])).
% 3.86/1.75  tff(c_1701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1689])).
% 3.86/1.75  tff(c_1702, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1635])).
% 3.86/1.75  tff(c_157, plain, (![B_71, A_72]: (~r1_tarski(B_71, A_72) | ~r2_hidden(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.86/1.75  tff(c_180, plain, (![C_17]: (~r1_tarski(k1_tarski(C_17), C_17))), inference(resolution, [status(thm)], [c_34, c_157])).
% 3.86/1.75  tff(c_1728, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1702, c_180])).
% 3.86/1.75  tff(c_1745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1728])).
% 3.86/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.86/1.75  
% 3.86/1.75  Inference rules
% 3.86/1.75  ----------------------
% 3.86/1.75  #Ref     : 0
% 3.86/1.75  #Sup     : 341
% 3.86/1.75  #Fact    : 2
% 3.86/1.75  #Define  : 0
% 3.86/1.75  #Split   : 11
% 3.86/1.75  #Chain   : 0
% 3.86/1.75  #Close   : 0
% 3.86/1.75  
% 3.86/1.75  Ordering : KBO
% 3.86/1.75  
% 3.86/1.75  Simplification rules
% 3.86/1.75  ----------------------
% 3.86/1.75  #Subsume      : 50
% 3.86/1.75  #Demod        : 185
% 3.86/1.75  #Tautology    : 133
% 3.86/1.75  #SimpNegUnit  : 24
% 3.86/1.75  #BackRed      : 57
% 3.86/1.75  
% 3.86/1.75  #Partial instantiations: 0
% 3.86/1.75  #Strategies tried      : 1
% 3.86/1.75  
% 3.86/1.75  Timing (in seconds)
% 3.86/1.75  ----------------------
% 4.16/1.75  Preprocessing        : 0.37
% 4.16/1.75  Parsing              : 0.19
% 4.16/1.75  CNF conversion       : 0.03
% 4.16/1.75  Main loop            : 0.54
% 4.16/1.75  Inferencing          : 0.19
% 4.16/1.75  Reduction            : 0.17
% 4.16/1.75  Demodulation         : 0.11
% 4.16/1.75  BG Simplification    : 0.03
% 4.16/1.75  Subsumption          : 0.10
% 4.16/1.75  Abstraction          : 0.03
% 4.16/1.75  MUC search           : 0.00
% 4.16/1.75  Cooper               : 0.00
% 4.16/1.75  Total                : 0.95
% 4.16/1.75  Index Insertion      : 0.00
% 4.16/1.75  Index Deletion       : 0.00
% 4.16/1.75  Index Matching       : 0.00
% 4.16/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
