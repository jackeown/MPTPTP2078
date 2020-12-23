%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:19 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 120 expanded)
%              Number of leaves         :   44 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 219 expanded)
%              Number of equality atoms :   34 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_89,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_159,plain,(
    ! [A_65] :
      ( v1_xboole_0(A_65)
      | r2_hidden('#skF_1'(A_65),A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [A_23] : k2_zfmisc_1(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_126,plain,(
    ! [A_56,B_57] : ~ r2_hidden(A_56,k2_zfmisc_1(A_56,B_57)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_129,plain,(
    ! [A_23] : ~ r2_hidden(A_23,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_126])).

tff(c_175,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_159,c_129])).

tff(c_84,plain,(
    k1_funct_1('#skF_9','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_86,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_90,plain,(
    v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_88,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_546,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_556,plain,(
    k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_88,c_546])).

tff(c_1735,plain,(
    ! [B_263,A_264,C_265] :
      ( k1_xboole_0 = B_263
      | k1_relset_1(A_264,B_263,C_265) = A_264
      | ~ v1_funct_2(C_265,A_264,B_263)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_264,B_263))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1742,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_88,c_1735])).

tff(c_1752,plain,
    ( k1_tarski('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_556,c_1742])).

tff(c_1754,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1752])).

tff(c_62,plain,(
    ! [A_35,B_36] : v1_relat_1(k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_259,plain,(
    ! [B_89,A_90] :
      ( v1_relat_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90))
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_262,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_88,c_259])).

tff(c_265,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_262])).

tff(c_92,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1544,plain,(
    ! [B_246,A_247] :
      ( r2_hidden(k1_funct_1(B_246,A_247),k2_relat_1(B_246))
      | ~ r2_hidden(A_247,k1_relat_1(B_246))
      | ~ v1_funct_1(B_246)
      | ~ v1_relat_1(B_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_562,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_572,plain,(
    k2_relset_1('#skF_6',k1_tarski('#skF_7'),'#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_88,c_562])).

tff(c_610,plain,(
    ! [A_148,B_149,C_150] :
      ( m1_subset_1(k2_relset_1(A_148,B_149,C_150),k1_zfmisc_1(B_149))
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_638,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(k1_tarski('#skF_7')))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6',k1_tarski('#skF_7')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_610])).

tff(c_652,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1(k1_tarski('#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_638])).

tff(c_58,plain,(
    ! [A_29,C_31,B_30] :
      ( m1_subset_1(A_29,C_31)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(C_31))
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_658,plain,(
    ! [A_29] :
      ( m1_subset_1(A_29,k1_tarski('#skF_7'))
      | ~ r2_hidden(A_29,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_652,c_58])).

tff(c_1548,plain,(
    ! [A_247] :
      ( m1_subset_1(k1_funct_1('#skF_9',A_247),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_247,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1544,c_658])).

tff(c_1556,plain,(
    ! [A_248] :
      ( m1_subset_1(k1_funct_1('#skF_9',A_248),k1_tarski('#skF_7'))
      | ~ r2_hidden(A_248,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_92,c_1548])).

tff(c_32,plain,(
    ! [C_16] : r2_hidden(C_16,k1_tarski(C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_134,plain,(
    ! [B_59,A_60] :
      ( ~ r2_hidden(B_59,A_60)
      | ~ v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [C_16] : ~ v1_xboole_0(k1_tarski(C_16)) ),
    inference(resolution,[status(thm)],[c_32,c_134])).

tff(c_266,plain,(
    ! [A_91,B_92] :
      ( r2_hidden(A_91,B_92)
      | v1_xboole_0(B_92)
      | ~ m1_subset_1(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_270,plain,(
    ! [A_91,A_12] :
      ( A_91 = A_12
      | v1_xboole_0(k1_tarski(A_12))
      | ~ m1_subset_1(A_91,k1_tarski(A_12)) ) ),
    inference(resolution,[status(thm)],[c_266,c_30])).

tff(c_284,plain,(
    ! [A_91,A_12] :
      ( A_91 = A_12
      | ~ m1_subset_1(A_91,k1_tarski(A_12)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_270])).

tff(c_1560,plain,(
    ! [A_248] :
      ( k1_funct_1('#skF_9',A_248) = '#skF_7'
      | ~ r2_hidden(A_248,k1_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1556,c_284])).

tff(c_1783,plain,(
    ! [A_266] :
      ( k1_funct_1('#skF_9',A_266) = '#skF_7'
      | ~ r2_hidden(A_266,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1754,c_1560])).

tff(c_1802,plain,(
    k1_funct_1('#skF_9','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_86,c_1783])).

tff(c_1814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1802])).

tff(c_1815,plain,(
    k1_tarski('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1752])).

tff(c_1843,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1815,c_141])).

tff(c_1851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_1843])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.65  
% 3.90/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.65  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.90/1.65  
% 3.90/1.65  %Foreground sorts:
% 3.90/1.65  
% 3.90/1.65  
% 3.90/1.65  %Background operators:
% 3.90/1.65  
% 3.90/1.65  
% 3.90/1.65  %Foreground operators:
% 3.90/1.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.90/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.90/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.90/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.90/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.90/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.90/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.90/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.90/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.90/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.90/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.90/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.90/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.90/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.90/1.65  tff('#skF_9', type, '#skF_9': $i).
% 3.90/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.90/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.90/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.90/1.65  tff('#skF_8', type, '#skF_8': $i).
% 3.90/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.90/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.90/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.65  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.90/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.90/1.65  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.90/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.90/1.65  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.90/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.90/1.65  
% 3.90/1.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.90/1.67  tff(f_65, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.90/1.67  tff(f_68, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.90/1.67  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 3.90/1.67  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.90/1.67  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.90/1.67  tff(f_89, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.90/1.67  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.90/1.67  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 3.90/1.67  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.90/1.67  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.90/1.67  tff(f_80, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.90/1.67  tff(f_53, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.90/1.67  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.90/1.67  tff(c_159, plain, (![A_65]: (v1_xboole_0(A_65) | r2_hidden('#skF_1'(A_65), A_65))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.67  tff(c_50, plain, (![A_23]: (k2_zfmisc_1(A_23, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.90/1.67  tff(c_126, plain, (![A_56, B_57]: (~r2_hidden(A_56, k2_zfmisc_1(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.90/1.67  tff(c_129, plain, (![A_23]: (~r2_hidden(A_23, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_126])).
% 3.90/1.67  tff(c_175, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_159, c_129])).
% 3.90/1.67  tff(c_84, plain, (k1_funct_1('#skF_9', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.90/1.67  tff(c_86, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.90/1.67  tff(c_90, plain, (v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.90/1.67  tff(c_88, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.90/1.67  tff(c_546, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.90/1.67  tff(c_556, plain, (k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_88, c_546])).
% 3.90/1.67  tff(c_1735, plain, (![B_263, A_264, C_265]: (k1_xboole_0=B_263 | k1_relset_1(A_264, B_263, C_265)=A_264 | ~v1_funct_2(C_265, A_264, B_263) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_264, B_263))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.90/1.67  tff(c_1742, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_88, c_1735])).
% 3.90/1.67  tff(c_1752, plain, (k1_tarski('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_556, c_1742])).
% 3.90/1.67  tff(c_1754, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_1752])).
% 3.90/1.67  tff(c_62, plain, (![A_35, B_36]: (v1_relat_1(k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.90/1.67  tff(c_259, plain, (![B_89, A_90]: (v1_relat_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.90/1.67  tff(c_262, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7')))), inference(resolution, [status(thm)], [c_88, c_259])).
% 3.90/1.67  tff(c_265, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_262])).
% 3.90/1.67  tff(c_92, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.90/1.67  tff(c_1544, plain, (![B_246, A_247]: (r2_hidden(k1_funct_1(B_246, A_247), k2_relat_1(B_246)) | ~r2_hidden(A_247, k1_relat_1(B_246)) | ~v1_funct_1(B_246) | ~v1_relat_1(B_246))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.90/1.67  tff(c_562, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.90/1.67  tff(c_572, plain, (k2_relset_1('#skF_6', k1_tarski('#skF_7'), '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_88, c_562])).
% 3.90/1.67  tff(c_610, plain, (![A_148, B_149, C_150]: (m1_subset_1(k2_relset_1(A_148, B_149, C_150), k1_zfmisc_1(B_149)) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.90/1.67  tff(c_638, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(k1_tarski('#skF_7'))) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', k1_tarski('#skF_7'))))), inference(superposition, [status(thm), theory('equality')], [c_572, c_610])).
% 3.90/1.67  tff(c_652, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1(k1_tarski('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_638])).
% 3.90/1.67  tff(c_58, plain, (![A_29, C_31, B_30]: (m1_subset_1(A_29, C_31) | ~m1_subset_1(B_30, k1_zfmisc_1(C_31)) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.90/1.67  tff(c_658, plain, (![A_29]: (m1_subset_1(A_29, k1_tarski('#skF_7')) | ~r2_hidden(A_29, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_652, c_58])).
% 3.90/1.67  tff(c_1548, plain, (![A_247]: (m1_subset_1(k1_funct_1('#skF_9', A_247), k1_tarski('#skF_7')) | ~r2_hidden(A_247, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1544, c_658])).
% 3.90/1.67  tff(c_1556, plain, (![A_248]: (m1_subset_1(k1_funct_1('#skF_9', A_248), k1_tarski('#skF_7')) | ~r2_hidden(A_248, k1_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_265, c_92, c_1548])).
% 3.90/1.67  tff(c_32, plain, (![C_16]: (r2_hidden(C_16, k1_tarski(C_16)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.90/1.67  tff(c_134, plain, (![B_59, A_60]: (~r2_hidden(B_59, A_60) | ~v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.67  tff(c_141, plain, (![C_16]: (~v1_xboole_0(k1_tarski(C_16)))), inference(resolution, [status(thm)], [c_32, c_134])).
% 3.90/1.67  tff(c_266, plain, (![A_91, B_92]: (r2_hidden(A_91, B_92) | v1_xboole_0(B_92) | ~m1_subset_1(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.90/1.67  tff(c_30, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.90/1.67  tff(c_270, plain, (![A_91, A_12]: (A_91=A_12 | v1_xboole_0(k1_tarski(A_12)) | ~m1_subset_1(A_91, k1_tarski(A_12)))), inference(resolution, [status(thm)], [c_266, c_30])).
% 3.90/1.67  tff(c_284, plain, (![A_91, A_12]: (A_91=A_12 | ~m1_subset_1(A_91, k1_tarski(A_12)))), inference(negUnitSimplification, [status(thm)], [c_141, c_270])).
% 3.90/1.67  tff(c_1560, plain, (![A_248]: (k1_funct_1('#skF_9', A_248)='#skF_7' | ~r2_hidden(A_248, k1_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_1556, c_284])).
% 3.90/1.67  tff(c_1783, plain, (![A_266]: (k1_funct_1('#skF_9', A_266)='#skF_7' | ~r2_hidden(A_266, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1754, c_1560])).
% 3.90/1.67  tff(c_1802, plain, (k1_funct_1('#skF_9', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_86, c_1783])).
% 3.90/1.67  tff(c_1814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1802])).
% 3.90/1.67  tff(c_1815, plain, (k1_tarski('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1752])).
% 3.90/1.67  tff(c_1843, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1815, c_141])).
% 3.90/1.67  tff(c_1851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_175, c_1843])).
% 3.90/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.67  
% 3.90/1.67  Inference rules
% 3.90/1.67  ----------------------
% 3.90/1.67  #Ref     : 0
% 3.90/1.67  #Sup     : 350
% 3.90/1.67  #Fact    : 2
% 3.90/1.67  #Define  : 0
% 3.90/1.67  #Split   : 18
% 3.90/1.67  #Chain   : 0
% 3.90/1.67  #Close   : 0
% 3.90/1.67  
% 3.90/1.67  Ordering : KBO
% 3.90/1.67  
% 3.90/1.67  Simplification rules
% 3.90/1.67  ----------------------
% 3.90/1.67  #Subsume      : 46
% 3.90/1.67  #Demod        : 240
% 3.90/1.67  #Tautology    : 149
% 3.90/1.67  #SimpNegUnit  : 26
% 3.90/1.67  #BackRed      : 83
% 3.90/1.67  
% 3.90/1.67  #Partial instantiations: 0
% 3.90/1.67  #Strategies tried      : 1
% 3.90/1.67  
% 3.90/1.67  Timing (in seconds)
% 3.90/1.67  ----------------------
% 3.90/1.68  Preprocessing        : 0.34
% 3.90/1.68  Parsing              : 0.17
% 3.90/1.68  CNF conversion       : 0.03
% 3.90/1.68  Main loop            : 0.57
% 3.90/1.68  Inferencing          : 0.20
% 3.90/1.68  Reduction            : 0.18
% 3.90/1.68  Demodulation         : 0.12
% 3.90/1.68  BG Simplification    : 0.03
% 3.90/1.68  Subsumption          : 0.10
% 3.90/1.68  Abstraction          : 0.03
% 3.90/1.68  MUC search           : 0.00
% 3.90/1.68  Cooper               : 0.00
% 3.90/1.68  Total                : 0.95
% 3.90/1.68  Index Insertion      : 0.00
% 3.90/1.68  Index Deletion       : 0.00
% 3.90/1.68  Index Matching       : 0.00
% 3.90/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
