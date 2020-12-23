%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:18 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   71 (  95 expanded)
%              Number of leaves         :   39 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 176 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_80,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    k1_funct_1('#skF_8','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_76,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_202,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_206,plain,(
    v5_relat_1('#skF_8',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_76,c_202])).

tff(c_74,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_48,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_160,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_163,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_76,c_160])).

tff(c_166,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_163])).

tff(c_80,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_78,plain,(
    v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_579,plain,(
    ! [A_1233,B_1234,C_1235] :
      ( k1_relset_1(A_1233,B_1234,C_1235) = k1_relat_1(C_1235)
      | ~ m1_subset_1(C_1235,k1_zfmisc_1(k2_zfmisc_1(A_1233,B_1234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_585,plain,(
    k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_579])).

tff(c_1486,plain,(
    ! [B_2405,A_2406,C_2407] :
      ( k1_xboole_0 = B_2405
      | k1_relset_1(A_2406,B_2405,C_2407) = A_2406
      | ~ v1_funct_2(C_2407,A_2406,B_2405)
      | ~ m1_subset_1(C_2407,k1_zfmisc_1(k2_zfmisc_1(A_2406,B_2405))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1491,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relset_1('#skF_5',k1_tarski('#skF_6'),'#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_76,c_1486])).

tff(c_1494,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_585,c_1491])).

tff(c_1495,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1494])).

tff(c_1452,plain,(
    ! [B_2371,C_2372,A_2373] :
      ( r2_hidden(k1_funct_1(B_2371,C_2372),A_2373)
      | ~ r2_hidden(C_2372,k1_relat_1(B_2371))
      | ~ v1_funct_1(B_2371)
      | ~ v5_relat_1(B_2371,A_2373)
      | ~ v1_relat_1(B_2371) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1607,plain,(
    ! [B_2631,C_2632,A_2633] :
      ( k1_funct_1(B_2631,C_2632) = A_2633
      | ~ r2_hidden(C_2632,k1_relat_1(B_2631))
      | ~ v1_funct_1(B_2631)
      | ~ v5_relat_1(B_2631,k1_tarski(A_2633))
      | ~ v1_relat_1(B_2631) ) ),
    inference(resolution,[status(thm)],[c_1452,c_28])).

tff(c_1609,plain,(
    ! [C_2632,A_2633] :
      ( k1_funct_1('#skF_8',C_2632) = A_2633
      | ~ r2_hidden(C_2632,'#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2633))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1495,c_1607])).

tff(c_1630,plain,(
    ! [C_2699,A_2700] :
      ( k1_funct_1('#skF_8',C_2699) = A_2700
      | ~ r2_hidden(C_2699,'#skF_5')
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2700)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_80,c_1609])).

tff(c_1648,plain,(
    ! [A_2732] :
      ( k1_funct_1('#skF_8','#skF_7') = A_2732
      | ~ v5_relat_1('#skF_8',k1_tarski(A_2732)) ) ),
    inference(resolution,[status(thm)],[c_74,c_1630])).

tff(c_1655,plain,(
    k1_funct_1('#skF_8','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_206,c_1648])).

tff(c_1659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1655])).

tff(c_1660,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1494])).

tff(c_30,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_102,plain,(
    ! [B_56,A_57] :
      ( ~ r1_tarski(B_56,A_57)
      | ~ r2_hidden(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_121,plain,(
    ! [C_13] : ~ r1_tarski(k1_tarski(C_13),C_13) ),
    inference(resolution,[status(thm)],[c_30,c_102])).

tff(c_1678,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1660,c_121])).

tff(c_1736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:52:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.63  
% 3.32/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_1 > #skF_4
% 3.32/1.63  
% 3.32/1.63  %Foreground sorts:
% 3.32/1.63  
% 3.32/1.63  
% 3.32/1.63  %Background operators:
% 3.32/1.63  
% 3.32/1.63  
% 3.32/1.63  %Foreground operators:
% 3.32/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.32/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.32/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.32/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.32/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.32/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.32/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.32/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.32/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.32/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.32/1.63  tff('#skF_8', type, '#skF_8': $i).
% 3.32/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.32/1.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.32/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.32/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.63  
% 3.32/1.64  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.32/1.64  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.32/1.64  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.32/1.64  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.32/1.64  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.32/1.64  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.32/1.64  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.32/1.64  tff(f_75, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 3.32/1.64  tff(f_49, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.32/1.64  tff(f_80, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.32/1.64  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.32/1.64  tff(c_72, plain, (k1_funct_1('#skF_8', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.32/1.64  tff(c_76, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.32/1.64  tff(c_202, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.32/1.64  tff(c_206, plain, (v5_relat_1('#skF_8', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_202])).
% 3.32/1.64  tff(c_74, plain, (r2_hidden('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.32/1.64  tff(c_48, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.32/1.64  tff(c_160, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.32/1.64  tff(c_163, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_76, c_160])).
% 3.32/1.64  tff(c_166, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_163])).
% 3.32/1.64  tff(c_80, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.32/1.64  tff(c_78, plain, (v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.32/1.64  tff(c_579, plain, (![A_1233, B_1234, C_1235]: (k1_relset_1(A_1233, B_1234, C_1235)=k1_relat_1(C_1235) | ~m1_subset_1(C_1235, k1_zfmisc_1(k2_zfmisc_1(A_1233, B_1234))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.32/1.64  tff(c_585, plain, (k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_76, c_579])).
% 3.32/1.64  tff(c_1486, plain, (![B_2405, A_2406, C_2407]: (k1_xboole_0=B_2405 | k1_relset_1(A_2406, B_2405, C_2407)=A_2406 | ~v1_funct_2(C_2407, A_2406, B_2405) | ~m1_subset_1(C_2407, k1_zfmisc_1(k2_zfmisc_1(A_2406, B_2405))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.32/1.64  tff(c_1491, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relset_1('#skF_5', k1_tarski('#skF_6'), '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_1486])).
% 3.32/1.64  tff(c_1494, plain, (k1_tarski('#skF_6')=k1_xboole_0 | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_585, c_1491])).
% 3.32/1.64  tff(c_1495, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_1494])).
% 3.32/1.64  tff(c_1452, plain, (![B_2371, C_2372, A_2373]: (r2_hidden(k1_funct_1(B_2371, C_2372), A_2373) | ~r2_hidden(C_2372, k1_relat_1(B_2371)) | ~v1_funct_1(B_2371) | ~v5_relat_1(B_2371, A_2373) | ~v1_relat_1(B_2371))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.32/1.64  tff(c_28, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.64  tff(c_1607, plain, (![B_2631, C_2632, A_2633]: (k1_funct_1(B_2631, C_2632)=A_2633 | ~r2_hidden(C_2632, k1_relat_1(B_2631)) | ~v1_funct_1(B_2631) | ~v5_relat_1(B_2631, k1_tarski(A_2633)) | ~v1_relat_1(B_2631))), inference(resolution, [status(thm)], [c_1452, c_28])).
% 3.32/1.64  tff(c_1609, plain, (![C_2632, A_2633]: (k1_funct_1('#skF_8', C_2632)=A_2633 | ~r2_hidden(C_2632, '#skF_5') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', k1_tarski(A_2633)) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1495, c_1607])).
% 3.32/1.64  tff(c_1630, plain, (![C_2699, A_2700]: (k1_funct_1('#skF_8', C_2699)=A_2700 | ~r2_hidden(C_2699, '#skF_5') | ~v5_relat_1('#skF_8', k1_tarski(A_2700)))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_80, c_1609])).
% 3.32/1.64  tff(c_1648, plain, (![A_2732]: (k1_funct_1('#skF_8', '#skF_7')=A_2732 | ~v5_relat_1('#skF_8', k1_tarski(A_2732)))), inference(resolution, [status(thm)], [c_74, c_1630])).
% 3.32/1.64  tff(c_1655, plain, (k1_funct_1('#skF_8', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_206, c_1648])).
% 3.32/1.64  tff(c_1659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1655])).
% 3.32/1.64  tff(c_1660, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1494])).
% 3.32/1.64  tff(c_30, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.64  tff(c_102, plain, (![B_56, A_57]: (~r1_tarski(B_56, A_57) | ~r2_hidden(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.32/1.64  tff(c_121, plain, (![C_13]: (~r1_tarski(k1_tarski(C_13), C_13))), inference(resolution, [status(thm)], [c_30, c_102])).
% 3.32/1.64  tff(c_1678, plain, (~r1_tarski(k1_xboole_0, '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1660, c_121])).
% 3.32/1.64  tff(c_1736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1678])).
% 3.32/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.64  
% 3.32/1.64  Inference rules
% 3.32/1.64  ----------------------
% 3.32/1.64  #Ref     : 0
% 3.32/1.64  #Sup     : 231
% 3.32/1.64  #Fact    : 0
% 3.32/1.64  #Define  : 0
% 3.32/1.64  #Split   : 6
% 3.32/1.64  #Chain   : 0
% 3.32/1.64  #Close   : 0
% 3.32/1.64  
% 3.32/1.64  Ordering : KBO
% 3.32/1.64  
% 3.32/1.64  Simplification rules
% 3.32/1.64  ----------------------
% 3.32/1.64  #Subsume      : 41
% 3.32/1.64  #Demod        : 49
% 3.32/1.64  #Tautology    : 75
% 3.32/1.64  #SimpNegUnit  : 1
% 3.32/1.64  #BackRed      : 5
% 3.32/1.64  
% 3.32/1.64  #Partial instantiations: 1494
% 3.32/1.64  #Strategies tried      : 1
% 3.32/1.64  
% 3.32/1.64  Timing (in seconds)
% 3.32/1.64  ----------------------
% 3.32/1.65  Preprocessing        : 0.35
% 3.66/1.65  Parsing              : 0.18
% 3.66/1.65  CNF conversion       : 0.03
% 3.66/1.65  Main loop            : 0.48
% 3.66/1.65  Inferencing          : 0.23
% 3.66/1.65  Reduction            : 0.12
% 3.66/1.65  Demodulation         : 0.08
% 3.66/1.65  BG Simplification    : 0.03
% 3.66/1.65  Subsumption          : 0.07
% 3.66/1.65  Abstraction          : 0.03
% 3.66/1.65  MUC search           : 0.00
% 3.66/1.65  Cooper               : 0.00
% 3.66/1.65  Total                : 0.87
% 3.66/1.65  Index Insertion      : 0.00
% 3.66/1.65  Index Deletion       : 0.00
% 3.66/1.65  Index Matching       : 0.00
% 3.66/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
