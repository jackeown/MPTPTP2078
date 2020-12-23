%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:13 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 698 expanded)
%              Number of leaves         :   45 ( 256 expanded)
%              Depth                    :   15
%              Number of atoms          :  220 (1601 expanded)
%              Number of equality atoms :   74 ( 452 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(c_80,plain,(
    k1_funct_1('#skF_11','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    r2_hidden('#skF_10','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_86,plain,(
    v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_84,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_359,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_369,plain,(
    k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_84,c_359])).

tff(c_1785,plain,(
    ! [B_4613,A_4614,C_4615] :
      ( k1_xboole_0 = B_4613
      | k1_relset_1(A_4614,B_4613,C_4615) = A_4614
      | ~ v1_funct_2(C_4615,A_4614,B_4613)
      | ~ m1_subset_1(C_4615,k1_zfmisc_1(k2_zfmisc_1(A_4614,B_4613))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1792,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_84,c_1785])).

tff(c_1802,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_369,c_1792])).

tff(c_1804,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1802])).

tff(c_183,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_191,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_84,c_183])).

tff(c_88,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1429,plain,(
    ! [A_4546,D_4547] :
      ( r2_hidden(k1_funct_1(A_4546,D_4547),k2_relat_1(A_4546))
      | ~ r2_hidden(D_4547,k1_relat_1(A_4546))
      | ~ v1_funct_1(A_4546)
      | ~ v1_relat_1(A_4546) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_282,plain,(
    ! [A_121,B_122,C_123] :
      ( k2_relset_1(A_121,B_122,C_123) = k2_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_292,plain,(
    k2_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = k2_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_84,c_282])).

tff(c_378,plain,(
    ! [A_139,B_140,C_141] :
      ( m1_subset_1(k2_relset_1(A_139,B_140,C_141),k1_zfmisc_1(B_140))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_411,plain,
    ( m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1(k1_tarski('#skF_9')))
    | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k1_tarski('#skF_9')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_378])).

tff(c_427,plain,(
    m1_subset_1(k2_relat_1('#skF_11'),k1_zfmisc_1(k1_tarski('#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_411])).

tff(c_40,plain,(
    ! [A_20,C_22,B_21] :
      ( m1_subset_1(A_20,C_22)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(C_22))
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_430,plain,(
    ! [A_20] :
      ( m1_subset_1(A_20,k1_tarski('#skF_9'))
      | ~ r2_hidden(A_20,k2_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_427,c_40])).

tff(c_1433,plain,(
    ! [D_4547] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_4547),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_4547,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_1429,c_430])).

tff(c_1441,plain,(
    ! [D_4548] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_4548),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_4548,k1_relat_1('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_88,c_1433])).

tff(c_131,plain,(
    ! [A_88] : k2_tarski(A_88,A_88) = k1_tarski(A_88) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_120,plain,(
    ! [D_82,A_83] : r2_hidden(D_82,k2_tarski(A_83,D_82)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_83,D_82] : ~ v1_xboole_0(k2_tarski(A_83,D_82)) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_139,plain,(
    ! [A_88] : ~ v1_xboole_0(k1_tarski(A_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_124])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_209,plain,(
    ! [D_106,B_107,A_108] :
      ( D_106 = B_107
      | D_106 = A_108
      | ~ r2_hidden(D_106,k2_tarski(A_108,B_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_237,plain,(
    ! [D_109,A_110] :
      ( D_109 = A_110
      | D_109 = A_110
      | ~ r2_hidden(D_109,k1_tarski(A_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_209])).

tff(c_241,plain,(
    ! [A_18,A_110] :
      ( A_18 = A_110
      | v1_xboole_0(k1_tarski(A_110))
      | ~ m1_subset_1(A_18,k1_tarski(A_110)) ) ),
    inference(resolution,[status(thm)],[c_38,c_237])).

tff(c_251,plain,(
    ! [A_18,A_110] :
      ( A_18 = A_110
      | ~ m1_subset_1(A_18,k1_tarski(A_110)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_241])).

tff(c_1445,plain,(
    ! [D_4548] :
      ( k1_funct_1('#skF_11',D_4548) = '#skF_9'
      | ~ r2_hidden(D_4548,k1_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_1441,c_251])).

tff(c_1838,plain,(
    ! [D_4616] :
      ( k1_funct_1('#skF_11',D_4616) = '#skF_9'
      | ~ r2_hidden(D_4616,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1804,c_1445])).

tff(c_1849,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_82,c_1838])).

tff(c_1859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1849])).

tff(c_1860,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1802])).

tff(c_36,plain,(
    ! [B_17,A_16] :
      ( k2_zfmisc_1(k1_tarski(B_17),A_16) != k1_xboole_0
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1885,plain,(
    ! [A_16] :
      ( k2_zfmisc_1(k1_xboole_0,A_16) != k1_xboole_0
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1860,c_36])).

tff(c_1910,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1885])).

tff(c_1896,plain,(
    ! [A_16] : k1_xboole_0 = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1885])).

tff(c_2422,plain,(
    ! [A_9101] : A_9101 = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_1910,c_1896])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1446,plain,(
    ! [D_4549] :
      ( k1_funct_1('#skF_11',D_4549) = '#skF_9'
      | ~ r2_hidden(D_4549,k1_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_1441,c_251])).

tff(c_1456,plain,
    ( k1_funct_1('#skF_11','#skF_1'(k1_relat_1('#skF_11'))) = '#skF_9'
    | v1_xboole_0(k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_4,c_1446])).

tff(c_1457,plain,(
    v1_xboole_0(k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_1456])).

tff(c_431,plain,(
    ! [A_142] :
      ( m1_subset_1(A_142,k1_tarski('#skF_9'))
      | ~ r2_hidden(A_142,k2_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_427,c_40])).

tff(c_441,plain,
    ( m1_subset_1('#skF_1'(k2_relat_1('#skF_11')),k1_tarski('#skF_9'))
    | v1_xboole_0(k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_4,c_431])).

tff(c_448,plain,(
    v1_xboole_0(k2_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_441])).

tff(c_115,plain,(
    ! [B_80,A_81] :
      ( ~ r2_hidden(B_80,A_81)
      | ~ v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_82,c_115])).

tff(c_781,plain,(
    ! [B_205,A_206,C_207] :
      ( k1_xboole_0 = B_205
      | k1_relset_1(A_206,B_205,C_207) = A_206
      | ~ v1_funct_2(C_207,A_206,B_205)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_788,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relset_1('#skF_8',k1_tarski('#skF_9'),'#skF_11') = '#skF_8'
    | ~ v1_funct_2('#skF_11','#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_84,c_781])).

tff(c_798,plain,
    ( k1_tarski('#skF_9') = k1_xboole_0
    | k1_relat_1('#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_369,c_788])).

tff(c_800,plain,(
    k1_relat_1('#skF_11') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_798])).

tff(c_458,plain,(
    ! [A_152,D_153] :
      ( r2_hidden(k1_funct_1(A_152,D_153),k2_relat_1(A_152))
      | ~ r2_hidden(D_153,k1_relat_1(A_152))
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_462,plain,(
    ! [D_153] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_153),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_153,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_458,c_430])).

tff(c_470,plain,(
    ! [D_154] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_154),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_154,k1_relat_1('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_88,c_462])).

tff(c_475,plain,(
    ! [D_155] :
      ( k1_funct_1('#skF_11',D_155) = '#skF_9'
      | ~ r2_hidden(D_155,k1_relat_1('#skF_11')) ) ),
    inference(resolution,[status(thm)],[c_470,c_251])).

tff(c_485,plain,
    ( k1_funct_1('#skF_11','#skF_1'(k1_relat_1('#skF_11'))) = '#skF_9'
    | v1_xboole_0(k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_4,c_475])).

tff(c_486,plain,(
    v1_xboole_0(k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_802,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_486])).

tff(c_805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_802])).

tff(c_806,plain,(
    k1_tarski('#skF_9') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_798])).

tff(c_827,plain,(
    ! [A_16] :
      ( k2_zfmisc_1(k1_xboole_0,A_16) != k1_xboole_0
      | k1_xboole_0 = A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_806,c_36])).

tff(c_1115,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_827])).

tff(c_842,plain,(
    ! [A_208] : k1_xboole_0 = A_208 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_827])).

tff(c_1125,plain,(
    ! [A_2363] : A_2363 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1115,c_842])).

tff(c_1323,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1125,c_80])).

tff(c_1325,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_1324,plain,(
    k1_funct_1('#skF_11','#skF_1'(k1_relat_1('#skF_11'))) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_468,plain,(
    ! [D_153] :
      ( m1_subset_1(k1_funct_1('#skF_11',D_153),k1_tarski('#skF_9'))
      | ~ r2_hidden(D_153,k1_relat_1('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_88,c_462])).

tff(c_1331,plain,
    ( m1_subset_1('#skF_9',k1_tarski('#skF_9'))
    | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_11')),k1_relat_1('#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1324,c_468])).

tff(c_1340,plain,(
    ~ r2_hidden('#skF_1'(k1_relat_1('#skF_11')),k1_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_1331])).

tff(c_1346,plain,(
    v1_xboole_0(k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_4,c_1340])).

tff(c_1353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1325,c_1346])).

tff(c_1355,plain,(
    r2_hidden('#skF_1'(k1_relat_1('#skF_11')),k1_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_1331])).

tff(c_42,plain,(
    ! [A_23,D_62] :
      ( r2_hidden(k1_funct_1(A_23,D_62),k2_relat_1(A_23))
      | ~ r2_hidden(D_62,k1_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1334,plain,
    ( r2_hidden('#skF_9',k2_relat_1('#skF_11'))
    | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_11')),k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_1324,c_42])).

tff(c_1338,plain,
    ( r2_hidden('#skF_9',k2_relat_1('#skF_11'))
    | ~ r2_hidden('#skF_1'(k1_relat_1('#skF_11')),k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_88,c_1334])).

tff(c_1377,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1355,c_1338])).

tff(c_1383,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_1377,c_2])).

tff(c_1389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_1383])).

tff(c_1391,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_1390,plain,(
    m1_subset_1('#skF_1'(k2_relat_1('#skF_11')),k1_tarski('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_441])).

tff(c_1395,plain,(
    '#skF_1'(k2_relat_1('#skF_11')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1390,c_251])).

tff(c_1402,plain,
    ( v1_xboole_0(k2_relat_1('#skF_11'))
    | r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1395,c_4])).

tff(c_1405,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_1391,c_1402])).

tff(c_1537,plain,(
    ! [A_4572,C_4573] :
      ( r2_hidden('#skF_7'(A_4572,k2_relat_1(A_4572),C_4573),k1_relat_1(A_4572))
      | ~ r2_hidden(C_4573,k2_relat_1(A_4572))
      | ~ v1_funct_1(A_4572)
      | ~ v1_relat_1(A_4572) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1553,plain,(
    ! [A_4574,C_4575] :
      ( ~ v1_xboole_0(k1_relat_1(A_4574))
      | ~ r2_hidden(C_4575,k2_relat_1(A_4574))
      | ~ v1_funct_1(A_4574)
      | ~ v1_relat_1(A_4574) ) ),
    inference(resolution,[status(thm)],[c_1537,c_2])).

tff(c_1559,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_1405,c_1553])).

tff(c_1572,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_88,c_1457,c_1559])).

tff(c_1573,plain,(
    k1_funct_1('#skF_11','#skF_1'(k1_relat_1('#skF_11'))) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1456])).

tff(c_2508,plain,(
    k1_funct_1('#skF_11','#skF_10') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_2422,c_1573])).

tff(c_2660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.90  
% 4.82/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.91  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 4.82/1.91  
% 4.82/1.91  %Foreground sorts:
% 4.82/1.91  
% 4.82/1.91  
% 4.82/1.91  %Background operators:
% 4.82/1.91  
% 4.82/1.91  
% 4.82/1.91  %Foreground operators:
% 4.82/1.91  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.82/1.91  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.82/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.82/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.91  tff('#skF_11', type, '#skF_11': $i).
% 4.82/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.82/1.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.82/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.82/1.91  tff('#skF_10', type, '#skF_10': $i).
% 4.82/1.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.82/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.82/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.82/1.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.82/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.82/1.91  tff('#skF_9', type, '#skF_9': $i).
% 4.82/1.91  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.82/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.91  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.82/1.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.82/1.91  tff('#skF_8', type, '#skF_8': $i).
% 4.82/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.82/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.82/1.91  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.82/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.82/1.91  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.82/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.82/1.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.82/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.91  
% 4.82/1.93  tff(f_131, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 4.82/1.93  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.82/1.93  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.82/1.93  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.82/1.93  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.82/1.93  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 4.82/1.93  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.82/1.93  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.82/1.93  tff(f_71, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.82/1.93  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.82/1.93  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 4.82/1.93  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.82/1.93  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.82/1.93  tff(f_59, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 4.82/1.93  tff(c_80, plain, (k1_funct_1('#skF_11', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.82/1.93  tff(c_32, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.82/1.93  tff(c_82, plain, (r2_hidden('#skF_10', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.82/1.93  tff(c_86, plain, (v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.82/1.93  tff(c_84, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.82/1.93  tff(c_359, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.82/1.93  tff(c_369, plain, (k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_84, c_359])).
% 4.82/1.93  tff(c_1785, plain, (![B_4613, A_4614, C_4615]: (k1_xboole_0=B_4613 | k1_relset_1(A_4614, B_4613, C_4615)=A_4614 | ~v1_funct_2(C_4615, A_4614, B_4613) | ~m1_subset_1(C_4615, k1_zfmisc_1(k2_zfmisc_1(A_4614, B_4613))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.82/1.93  tff(c_1792, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_84, c_1785])).
% 4.82/1.93  tff(c_1802, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_369, c_1792])).
% 4.82/1.93  tff(c_1804, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_1802])).
% 4.82/1.93  tff(c_183, plain, (![C_98, A_99, B_100]: (v1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.82/1.93  tff(c_191, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_84, c_183])).
% 4.82/1.93  tff(c_88, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.82/1.93  tff(c_1429, plain, (![A_4546, D_4547]: (r2_hidden(k1_funct_1(A_4546, D_4547), k2_relat_1(A_4546)) | ~r2_hidden(D_4547, k1_relat_1(A_4546)) | ~v1_funct_1(A_4546) | ~v1_relat_1(A_4546))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.82/1.93  tff(c_282, plain, (![A_121, B_122, C_123]: (k2_relset_1(A_121, B_122, C_123)=k2_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.82/1.93  tff(c_292, plain, (k2_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')=k2_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_84, c_282])).
% 4.82/1.93  tff(c_378, plain, (![A_139, B_140, C_141]: (m1_subset_1(k2_relset_1(A_139, B_140, C_141), k1_zfmisc_1(B_140)) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.82/1.93  tff(c_411, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1(k1_tarski('#skF_9'))) | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k1_tarski('#skF_9'))))), inference(superposition, [status(thm), theory('equality')], [c_292, c_378])).
% 4.82/1.93  tff(c_427, plain, (m1_subset_1(k2_relat_1('#skF_11'), k1_zfmisc_1(k1_tarski('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_411])).
% 4.82/1.93  tff(c_40, plain, (![A_20, C_22, B_21]: (m1_subset_1(A_20, C_22) | ~m1_subset_1(B_21, k1_zfmisc_1(C_22)) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.82/1.93  tff(c_430, plain, (![A_20]: (m1_subset_1(A_20, k1_tarski('#skF_9')) | ~r2_hidden(A_20, k2_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_427, c_40])).
% 4.82/1.93  tff(c_1433, plain, (![D_4547]: (m1_subset_1(k1_funct_1('#skF_11', D_4547), k1_tarski('#skF_9')) | ~r2_hidden(D_4547, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_1429, c_430])).
% 4.82/1.93  tff(c_1441, plain, (![D_4548]: (m1_subset_1(k1_funct_1('#skF_11', D_4548), k1_tarski('#skF_9')) | ~r2_hidden(D_4548, k1_relat_1('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_88, c_1433])).
% 4.82/1.93  tff(c_131, plain, (![A_88]: (k2_tarski(A_88, A_88)=k1_tarski(A_88))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.82/1.93  tff(c_120, plain, (![D_82, A_83]: (r2_hidden(D_82, k2_tarski(A_83, D_82)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.82/1.93  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.82/1.93  tff(c_124, plain, (![A_83, D_82]: (~v1_xboole_0(k2_tarski(A_83, D_82)))), inference(resolution, [status(thm)], [c_120, c_2])).
% 4.82/1.93  tff(c_139, plain, (![A_88]: (~v1_xboole_0(k1_tarski(A_88)))), inference(superposition, [status(thm), theory('equality')], [c_131, c_124])).
% 4.82/1.93  tff(c_38, plain, (![A_18, B_19]: (r2_hidden(A_18, B_19) | v1_xboole_0(B_19) | ~m1_subset_1(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.82/1.93  tff(c_24, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.82/1.93  tff(c_209, plain, (![D_106, B_107, A_108]: (D_106=B_107 | D_106=A_108 | ~r2_hidden(D_106, k2_tarski(A_108, B_107)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.82/1.93  tff(c_237, plain, (![D_109, A_110]: (D_109=A_110 | D_109=A_110 | ~r2_hidden(D_109, k1_tarski(A_110)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_209])).
% 4.82/1.93  tff(c_241, plain, (![A_18, A_110]: (A_18=A_110 | v1_xboole_0(k1_tarski(A_110)) | ~m1_subset_1(A_18, k1_tarski(A_110)))), inference(resolution, [status(thm)], [c_38, c_237])).
% 4.82/1.93  tff(c_251, plain, (![A_18, A_110]: (A_18=A_110 | ~m1_subset_1(A_18, k1_tarski(A_110)))), inference(negUnitSimplification, [status(thm)], [c_139, c_241])).
% 4.82/1.93  tff(c_1445, plain, (![D_4548]: (k1_funct_1('#skF_11', D_4548)='#skF_9' | ~r2_hidden(D_4548, k1_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_1441, c_251])).
% 4.82/1.93  tff(c_1838, plain, (![D_4616]: (k1_funct_1('#skF_11', D_4616)='#skF_9' | ~r2_hidden(D_4616, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1804, c_1445])).
% 4.82/1.93  tff(c_1849, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_82, c_1838])).
% 4.82/1.93  tff(c_1859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1849])).
% 4.82/1.93  tff(c_1860, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1802])).
% 4.82/1.93  tff(c_36, plain, (![B_17, A_16]: (k2_zfmisc_1(k1_tarski(B_17), A_16)!=k1_xboole_0 | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.82/1.93  tff(c_1885, plain, (![A_16]: (k2_zfmisc_1(k1_xboole_0, A_16)!=k1_xboole_0 | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_1860, c_36])).
% 4.82/1.93  tff(c_1910, plain, (k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1885])).
% 4.82/1.93  tff(c_1896, plain, (![A_16]: (k1_xboole_0=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1885])).
% 4.82/1.93  tff(c_2422, plain, (![A_9101]: (A_9101='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1910, c_1896])).
% 4.82/1.93  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.82/1.93  tff(c_1446, plain, (![D_4549]: (k1_funct_1('#skF_11', D_4549)='#skF_9' | ~r2_hidden(D_4549, k1_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_1441, c_251])).
% 4.82/1.93  tff(c_1456, plain, (k1_funct_1('#skF_11', '#skF_1'(k1_relat_1('#skF_11')))='#skF_9' | v1_xboole_0(k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_4, c_1446])).
% 4.82/1.93  tff(c_1457, plain, (v1_xboole_0(k1_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_1456])).
% 4.82/1.93  tff(c_431, plain, (![A_142]: (m1_subset_1(A_142, k1_tarski('#skF_9')) | ~r2_hidden(A_142, k2_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_427, c_40])).
% 4.82/1.93  tff(c_441, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_11')), k1_tarski('#skF_9')) | v1_xboole_0(k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_4, c_431])).
% 4.82/1.93  tff(c_448, plain, (v1_xboole_0(k2_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_441])).
% 4.82/1.93  tff(c_115, plain, (![B_80, A_81]: (~r2_hidden(B_80, A_81) | ~v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.82/1.93  tff(c_119, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_82, c_115])).
% 4.82/1.93  tff(c_781, plain, (![B_205, A_206, C_207]: (k1_xboole_0=B_205 | k1_relset_1(A_206, B_205, C_207)=A_206 | ~v1_funct_2(C_207, A_206, B_205) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.82/1.93  tff(c_788, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relset_1('#skF_8', k1_tarski('#skF_9'), '#skF_11')='#skF_8' | ~v1_funct_2('#skF_11', '#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_84, c_781])).
% 4.82/1.93  tff(c_798, plain, (k1_tarski('#skF_9')=k1_xboole_0 | k1_relat_1('#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_369, c_788])).
% 4.82/1.93  tff(c_800, plain, (k1_relat_1('#skF_11')='#skF_8'), inference(splitLeft, [status(thm)], [c_798])).
% 4.82/1.93  tff(c_458, plain, (![A_152, D_153]: (r2_hidden(k1_funct_1(A_152, D_153), k2_relat_1(A_152)) | ~r2_hidden(D_153, k1_relat_1(A_152)) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.82/1.93  tff(c_462, plain, (![D_153]: (m1_subset_1(k1_funct_1('#skF_11', D_153), k1_tarski('#skF_9')) | ~r2_hidden(D_153, k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_458, c_430])).
% 4.82/1.93  tff(c_470, plain, (![D_154]: (m1_subset_1(k1_funct_1('#skF_11', D_154), k1_tarski('#skF_9')) | ~r2_hidden(D_154, k1_relat_1('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_88, c_462])).
% 4.82/1.93  tff(c_475, plain, (![D_155]: (k1_funct_1('#skF_11', D_155)='#skF_9' | ~r2_hidden(D_155, k1_relat_1('#skF_11')))), inference(resolution, [status(thm)], [c_470, c_251])).
% 4.82/1.93  tff(c_485, plain, (k1_funct_1('#skF_11', '#skF_1'(k1_relat_1('#skF_11')))='#skF_9' | v1_xboole_0(k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_4, c_475])).
% 4.82/1.93  tff(c_486, plain, (v1_xboole_0(k1_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_485])).
% 4.82/1.93  tff(c_802, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_800, c_486])).
% 4.82/1.93  tff(c_805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_802])).
% 4.82/1.93  tff(c_806, plain, (k1_tarski('#skF_9')=k1_xboole_0), inference(splitRight, [status(thm)], [c_798])).
% 4.82/1.93  tff(c_827, plain, (![A_16]: (k2_zfmisc_1(k1_xboole_0, A_16)!=k1_xboole_0 | k1_xboole_0=A_16)), inference(superposition, [status(thm), theory('equality')], [c_806, c_36])).
% 4.82/1.93  tff(c_1115, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_827])).
% 4.82/1.93  tff(c_842, plain, (![A_208]: (k1_xboole_0=A_208)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_827])).
% 4.82/1.93  tff(c_1125, plain, (![A_2363]: (A_2363='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1115, c_842])).
% 4.82/1.93  tff(c_1323, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1125, c_80])).
% 4.82/1.93  tff(c_1325, plain, (~v1_xboole_0(k1_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_485])).
% 4.82/1.93  tff(c_1324, plain, (k1_funct_1('#skF_11', '#skF_1'(k1_relat_1('#skF_11')))='#skF_9'), inference(splitRight, [status(thm)], [c_485])).
% 4.82/1.93  tff(c_468, plain, (![D_153]: (m1_subset_1(k1_funct_1('#skF_11', D_153), k1_tarski('#skF_9')) | ~r2_hidden(D_153, k1_relat_1('#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_88, c_462])).
% 4.82/1.93  tff(c_1331, plain, (m1_subset_1('#skF_9', k1_tarski('#skF_9')) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_11')), k1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_1324, c_468])).
% 4.82/1.93  tff(c_1340, plain, (~r2_hidden('#skF_1'(k1_relat_1('#skF_11')), k1_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_1331])).
% 4.82/1.93  tff(c_1346, plain, (v1_xboole_0(k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_4, c_1340])).
% 4.82/1.93  tff(c_1353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1325, c_1346])).
% 4.82/1.93  tff(c_1355, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_11')), k1_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_1331])).
% 4.82/1.93  tff(c_42, plain, (![A_23, D_62]: (r2_hidden(k1_funct_1(A_23, D_62), k2_relat_1(A_23)) | ~r2_hidden(D_62, k1_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.82/1.93  tff(c_1334, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_11')) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_11')), k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_1324, c_42])).
% 4.82/1.93  tff(c_1338, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_11')) | ~r2_hidden('#skF_1'(k1_relat_1('#skF_11')), k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_88, c_1334])).
% 4.82/1.93  tff(c_1377, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1355, c_1338])).
% 4.82/1.93  tff(c_1383, plain, (~v1_xboole_0(k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_1377, c_2])).
% 4.82/1.93  tff(c_1389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_448, c_1383])).
% 4.82/1.93  tff(c_1391, plain, (~v1_xboole_0(k2_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_441])).
% 4.82/1.93  tff(c_1390, plain, (m1_subset_1('#skF_1'(k2_relat_1('#skF_11')), k1_tarski('#skF_9'))), inference(splitRight, [status(thm)], [c_441])).
% 4.82/1.93  tff(c_1395, plain, ('#skF_1'(k2_relat_1('#skF_11'))='#skF_9'), inference(resolution, [status(thm)], [c_1390, c_251])).
% 4.82/1.93  tff(c_1402, plain, (v1_xboole_0(k2_relat_1('#skF_11')) | r2_hidden('#skF_9', k2_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_1395, c_4])).
% 4.82/1.93  tff(c_1405, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_1391, c_1402])).
% 4.82/1.93  tff(c_1537, plain, (![A_4572, C_4573]: (r2_hidden('#skF_7'(A_4572, k2_relat_1(A_4572), C_4573), k1_relat_1(A_4572)) | ~r2_hidden(C_4573, k2_relat_1(A_4572)) | ~v1_funct_1(A_4572) | ~v1_relat_1(A_4572))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.82/1.93  tff(c_1553, plain, (![A_4574, C_4575]: (~v1_xboole_0(k1_relat_1(A_4574)) | ~r2_hidden(C_4575, k2_relat_1(A_4574)) | ~v1_funct_1(A_4574) | ~v1_relat_1(A_4574))), inference(resolution, [status(thm)], [c_1537, c_2])).
% 4.82/1.93  tff(c_1559, plain, (~v1_xboole_0(k1_relat_1('#skF_11')) | ~v1_funct_1('#skF_11') | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_1405, c_1553])).
% 4.82/1.93  tff(c_1572, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_88, c_1457, c_1559])).
% 4.82/1.93  tff(c_1573, plain, (k1_funct_1('#skF_11', '#skF_1'(k1_relat_1('#skF_11')))='#skF_9'), inference(splitRight, [status(thm)], [c_1456])).
% 4.82/1.93  tff(c_2508, plain, (k1_funct_1('#skF_11', '#skF_10')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_2422, c_1573])).
% 4.82/1.93  tff(c_2660, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_2508])).
% 4.82/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.82/1.93  
% 4.82/1.93  Inference rules
% 4.82/1.93  ----------------------
% 4.82/1.93  #Ref     : 0
% 4.82/1.93  #Sup     : 805
% 4.82/1.93  #Fact    : 2
% 4.82/1.93  #Define  : 0
% 4.82/1.93  #Split   : 9
% 4.82/1.93  #Chain   : 0
% 4.82/1.93  #Close   : 0
% 4.82/1.93  
% 4.82/1.93  Ordering : KBO
% 4.82/1.93  
% 4.82/1.93  Simplification rules
% 4.82/1.93  ----------------------
% 4.82/1.93  #Subsume      : 133
% 4.82/1.93  #Demod        : 166
% 4.82/1.93  #Tautology    : 94
% 4.82/1.93  #SimpNegUnit  : 23
% 4.82/1.93  #BackRed      : 26
% 4.82/1.93  
% 4.82/1.93  #Partial instantiations: 695
% 4.82/1.93  #Strategies tried      : 1
% 4.82/1.93  
% 4.82/1.93  Timing (in seconds)
% 4.82/1.93  ----------------------
% 4.82/1.93  Preprocessing        : 0.37
% 4.82/1.93  Parsing              : 0.19
% 4.82/1.93  CNF conversion       : 0.03
% 4.82/1.93  Main loop            : 0.73
% 4.82/1.93  Inferencing          : 0.30
% 4.82/1.93  Reduction            : 0.21
% 4.82/1.93  Demodulation         : 0.14
% 4.82/1.93  BG Simplification    : 0.04
% 4.82/1.93  Subsumption          : 0.13
% 4.82/1.94  Abstraction          : 0.04
% 4.82/1.94  MUC search           : 0.00
% 4.82/1.94  Cooper               : 0.00
% 4.82/1.94  Total                : 1.16
% 4.82/1.94  Index Insertion      : 0.00
% 4.82/1.94  Index Deletion       : 0.00
% 4.82/1.94  Index Matching       : 0.00
% 4.82/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
