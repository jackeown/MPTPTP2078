%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:36 EST 2020

% Result     : Theorem 9.92s
% Output     : CNFRefutation 10.09s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 182 expanded)
%              Number of leaves         :   41 (  83 expanded)
%              Depth                    :   22
%              Number of atoms          :  160 ( 414 expanded)
%              Number of equality atoms :   79 ( 162 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_40,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_72,plain,(
    v1_funct_2('#skF_10',k1_tarski('#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_70,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_8'),'#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_101,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_105,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_101])).

tff(c_106,plain,(
    ! [A_76] :
      ( k1_relat_1(A_76) = k1_xboole_0
      | k2_relat_1(A_76) != k1_xboole_0
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_110,plain,
    ( k1_relat_1('#skF_10') = k1_xboole_0
    | k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_106])).

tff(c_111,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_3'(A_10,B_11),A_10)
      | k1_xboole_0 = A_10
      | k1_tarski(B_11) = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_74,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    ! [A_14,C_50] :
      ( r2_hidden('#skF_7'(A_14,k2_relat_1(A_14),C_50),k1_relat_1(A_14))
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [A_14,D_53] :
      ( r2_hidden(k1_funct_1(A_14,D_53),k2_relat_1(A_14))
      | ~ r2_hidden(D_53,k1_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_144,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_148,plain,(
    k1_relset_1(k1_tarski('#skF_8'),'#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_144])).

tff(c_225,plain,(
    ! [B_117,A_118,C_119] :
      ( k1_xboole_0 = B_117
      | k1_relset_1(A_118,B_117,C_119) = A_118
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_228,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1(k1_tarski('#skF_8'),'#skF_9','#skF_10') = k1_tarski('#skF_8')
    | ~ v1_funct_2('#skF_10',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_225])).

tff(c_231,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_tarski('#skF_8') = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_148,c_228])).

tff(c_232,plain,(
    k1_tarski('#skF_8') = k1_relat_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_231])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_267,plain,(
    ! [C_123] :
      ( C_123 = '#skF_8'
      | ~ r2_hidden(C_123,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_4])).

tff(c_278,plain,(
    ! [C_50] :
      ( '#skF_7'('#skF_10',k2_relat_1('#skF_10'),C_50) = '#skF_8'
      | ~ r2_hidden(C_50,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_34,c_267])).

tff(c_356,plain,(
    ! [C_125] :
      ( '#skF_7'('#skF_10',k2_relat_1('#skF_10'),C_125) = '#skF_8'
      | ~ r2_hidden(C_125,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_74,c_278])).

tff(c_364,plain,(
    ! [D_53] :
      ( '#skF_7'('#skF_10',k2_relat_1('#skF_10'),k1_funct_1('#skF_10',D_53)) = '#skF_8'
      | ~ r2_hidden(D_53,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_30,c_356])).

tff(c_562,plain,(
    ! [D_138] :
      ( '#skF_7'('#skF_10',k2_relat_1('#skF_10'),k1_funct_1('#skF_10',D_138)) = '#skF_8'
      | ~ r2_hidden(D_138,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_74,c_364])).

tff(c_32,plain,(
    ! [A_14,C_50] :
      ( k1_funct_1(A_14,'#skF_7'(A_14,k2_relat_1(A_14),C_50)) = C_50
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_568,plain,(
    ! [D_138] :
      ( k1_funct_1('#skF_10',D_138) = k1_funct_1('#skF_10','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_10',D_138),k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_138,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_32])).

tff(c_5356,plain,(
    ! [D_8286] :
      ( k1_funct_1('#skF_10',D_8286) = k1_funct_1('#skF_10','#skF_8')
      | ~ r2_hidden(k1_funct_1('#skF_10',D_8286),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_8286,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_74,c_568])).

tff(c_5373,plain,(
    ! [D_53] :
      ( k1_funct_1('#skF_10',D_53) = k1_funct_1('#skF_10','#skF_8')
      | ~ r2_hidden(D_53,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_30,c_5356])).

tff(c_5381,plain,(
    ! [D_8321] :
      ( k1_funct_1('#skF_10',D_8321) = k1_funct_1('#skF_10','#skF_8')
      | ~ r2_hidden(D_8321,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_74,c_5373])).

tff(c_5416,plain,(
    ! [C_50] :
      ( k1_funct_1('#skF_10','#skF_7'('#skF_10',k2_relat_1('#skF_10'),C_50)) = k1_funct_1('#skF_10','#skF_8')
      | ~ r2_hidden(C_50,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_34,c_5381])).

tff(c_6195,plain,(
    ! [C_8674] :
      ( k1_funct_1('#skF_10','#skF_7'('#skF_10',k2_relat_1('#skF_10'),C_8674)) = k1_funct_1('#skF_10','#skF_8')
      | ~ r2_hidden(C_8674,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_74,c_5416])).

tff(c_6235,plain,(
    ! [C_8674] :
      ( k1_funct_1('#skF_10','#skF_8') = C_8674
      | ~ r2_hidden(C_8674,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_8674,k2_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6195,c_32])).

tff(c_6290,plain,(
    ! [C_8709] :
      ( k1_funct_1('#skF_10','#skF_8') = C_8709
      | ~ r2_hidden(C_8709,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_74,c_6235])).

tff(c_6329,plain,(
    ! [B_11] :
      ( '#skF_3'(k2_relat_1('#skF_10'),B_11) = k1_funct_1('#skF_10','#skF_8')
      | k2_relat_1('#skF_10') = k1_xboole_0
      | k2_relat_1('#skF_10') = k1_tarski(B_11) ) ),
    inference(resolution,[status(thm)],[c_24,c_6290])).

tff(c_6346,plain,(
    ! [B_8744] :
      ( '#skF_3'(k2_relat_1('#skF_10'),B_8744) = k1_funct_1('#skF_10','#skF_8')
      | k2_relat_1('#skF_10') = k1_tarski(B_8744) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_6329])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( '#skF_3'(A_10,B_11) != B_11
      | k1_xboole_0 = A_10
      | k1_tarski(B_11) = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6360,plain,(
    ! [B_8744] :
      ( k1_funct_1('#skF_10','#skF_8') != B_8744
      | k2_relat_1('#skF_10') = k1_xboole_0
      | k2_relat_1('#skF_10') = k1_tarski(B_8744)
      | k2_relat_1('#skF_10') = k1_tarski(B_8744) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6346,c_22])).

tff(c_6412,plain,(
    k1_tarski(k1_funct_1('#skF_10','#skF_8')) = k2_relat_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_6360])).

tff(c_132,plain,(
    ! [A_86,B_87,C_88] :
      ( k2_relset_1(A_86,B_87,C_88) = k2_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_136,plain,(
    k2_relset_1(k1_tarski('#skF_8'),'#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_132])).

tff(c_66,plain,(
    k2_relset_1(k1_tarski('#skF_8'),'#skF_9','#skF_10') != k1_tarski(k1_funct_1('#skF_10','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_137,plain,(
    k1_tarski(k1_funct_1('#skF_10','#skF_8')) != k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_66])).

tff(c_6416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6412,c_137])).

tff(c_6417,plain,(
    k1_relat_1('#skF_10') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_6461,plain,(
    ! [A_8831,B_8832,C_8833] :
      ( k1_relset_1(A_8831,B_8832,C_8833) = k1_relat_1(C_8833)
      | ~ m1_subset_1(C_8833,k1_zfmisc_1(k2_zfmisc_1(A_8831,B_8832))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6464,plain,(
    k1_relset_1(k1_tarski('#skF_8'),'#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_6461])).

tff(c_6466,plain,(
    k1_relset_1(k1_tarski('#skF_8'),'#skF_9','#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6417,c_6464])).

tff(c_6589,plain,(
    ! [B_8860,A_8861,C_8862] :
      ( k1_xboole_0 = B_8860
      | k1_relset_1(A_8861,B_8860,C_8862) = A_8861
      | ~ v1_funct_2(C_8862,A_8861,B_8860)
      | ~ m1_subset_1(C_8862,k1_zfmisc_1(k2_zfmisc_1(A_8861,B_8860))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6592,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1(k1_tarski('#skF_8'),'#skF_9','#skF_10') = k1_tarski('#skF_8')
    | ~ v1_funct_2('#skF_10',k1_tarski('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_6589])).

tff(c_6595,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6466,c_6592])).

tff(c_6596,plain,(
    k1_tarski('#skF_8') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6595])).

tff(c_20,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_tarski(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6621,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6596,c_20])).

tff(c_6630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6621])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.92/3.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.91  
% 9.92/3.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.92/3.93  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_7 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 9.92/3.93  
% 9.92/3.93  %Foreground sorts:
% 9.92/3.93  
% 9.92/3.93  
% 9.92/3.93  %Background operators:
% 9.92/3.93  
% 9.92/3.93  
% 9.92/3.93  %Foreground operators:
% 9.92/3.93  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.92/3.93  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 9.92/3.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.92/3.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.92/3.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.92/3.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.92/3.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.92/3.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.92/3.93  tff('#skF_10', type, '#skF_10': $i).
% 9.92/3.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.92/3.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.92/3.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.92/3.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.92/3.93  tff('#skF_9', type, '#skF_9': $i).
% 9.92/3.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.92/3.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.92/3.93  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.92/3.93  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.92/3.93  tff('#skF_8', type, '#skF_8': $i).
% 9.92/3.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.92/3.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.92/3.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.92/3.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.92/3.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.92/3.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.92/3.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.92/3.93  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.92/3.93  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.92/3.93  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.92/3.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.92/3.93  
% 10.09/3.95  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.09/3.95  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 10.09/3.95  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.09/3.95  tff(f_60, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 10.09/3.95  tff(f_54, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 10.09/3.95  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 10.09/3.95  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.09/3.95  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.09/3.95  tff(f_33, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 10.09/3.95  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.09/3.95  tff(f_40, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 10.09/3.95  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.09/3.95  tff(c_68, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.09/3.95  tff(c_72, plain, (v1_funct_2('#skF_10', k1_tarski('#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.09/3.95  tff(c_70, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_8'), '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.09/3.95  tff(c_101, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.09/3.95  tff(c_105, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_101])).
% 10.09/3.95  tff(c_106, plain, (![A_76]: (k1_relat_1(A_76)=k1_xboole_0 | k2_relat_1(A_76)!=k1_xboole_0 | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.09/3.95  tff(c_110, plain, (k1_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')!=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_106])).
% 10.09/3.95  tff(c_111, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_110])).
% 10.09/3.95  tff(c_24, plain, (![A_10, B_11]: (r2_hidden('#skF_3'(A_10, B_11), A_10) | k1_xboole_0=A_10 | k1_tarski(B_11)=A_10)), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.09/3.95  tff(c_74, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.09/3.95  tff(c_34, plain, (![A_14, C_50]: (r2_hidden('#skF_7'(A_14, k2_relat_1(A_14), C_50), k1_relat_1(A_14)) | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.09/3.95  tff(c_30, plain, (![A_14, D_53]: (r2_hidden(k1_funct_1(A_14, D_53), k2_relat_1(A_14)) | ~r2_hidden(D_53, k1_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.09/3.95  tff(c_144, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.09/3.95  tff(c_148, plain, (k1_relset_1(k1_tarski('#skF_8'), '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_144])).
% 10.09/3.95  tff(c_225, plain, (![B_117, A_118, C_119]: (k1_xboole_0=B_117 | k1_relset_1(A_118, B_117, C_119)=A_118 | ~v1_funct_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.09/3.95  tff(c_228, plain, (k1_xboole_0='#skF_9' | k1_relset_1(k1_tarski('#skF_8'), '#skF_9', '#skF_10')=k1_tarski('#skF_8') | ~v1_funct_2('#skF_10', k1_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_70, c_225])).
% 10.09/3.95  tff(c_231, plain, (k1_xboole_0='#skF_9' | k1_tarski('#skF_8')=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_148, c_228])).
% 10.09/3.95  tff(c_232, plain, (k1_tarski('#skF_8')=k1_relat_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_68, c_231])).
% 10.09/3.95  tff(c_4, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.09/3.95  tff(c_267, plain, (![C_123]: (C_123='#skF_8' | ~r2_hidden(C_123, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_232, c_4])).
% 10.09/3.95  tff(c_278, plain, (![C_50]: ('#skF_7'('#skF_10', k2_relat_1('#skF_10'), C_50)='#skF_8' | ~r2_hidden(C_50, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_34, c_267])).
% 10.09/3.95  tff(c_356, plain, (![C_125]: ('#skF_7'('#skF_10', k2_relat_1('#skF_10'), C_125)='#skF_8' | ~r2_hidden(C_125, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_74, c_278])).
% 10.09/3.95  tff(c_364, plain, (![D_53]: ('#skF_7'('#skF_10', k2_relat_1('#skF_10'), k1_funct_1('#skF_10', D_53))='#skF_8' | ~r2_hidden(D_53, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_30, c_356])).
% 10.09/3.95  tff(c_562, plain, (![D_138]: ('#skF_7'('#skF_10', k2_relat_1('#skF_10'), k1_funct_1('#skF_10', D_138))='#skF_8' | ~r2_hidden(D_138, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_74, c_364])).
% 10.09/3.95  tff(c_32, plain, (![A_14, C_50]: (k1_funct_1(A_14, '#skF_7'(A_14, k2_relat_1(A_14), C_50))=C_50 | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.09/3.95  tff(c_568, plain, (![D_138]: (k1_funct_1('#skF_10', D_138)=k1_funct_1('#skF_10', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_10', D_138), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_138, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_562, c_32])).
% 10.09/3.95  tff(c_5356, plain, (![D_8286]: (k1_funct_1('#skF_10', D_8286)=k1_funct_1('#skF_10', '#skF_8') | ~r2_hidden(k1_funct_1('#skF_10', D_8286), k2_relat_1('#skF_10')) | ~r2_hidden(D_8286, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_74, c_568])).
% 10.09/3.95  tff(c_5373, plain, (![D_53]: (k1_funct_1('#skF_10', D_53)=k1_funct_1('#skF_10', '#skF_8') | ~r2_hidden(D_53, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_30, c_5356])).
% 10.09/3.95  tff(c_5381, plain, (![D_8321]: (k1_funct_1('#skF_10', D_8321)=k1_funct_1('#skF_10', '#skF_8') | ~r2_hidden(D_8321, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_74, c_5373])).
% 10.09/3.95  tff(c_5416, plain, (![C_50]: (k1_funct_1('#skF_10', '#skF_7'('#skF_10', k2_relat_1('#skF_10'), C_50))=k1_funct_1('#skF_10', '#skF_8') | ~r2_hidden(C_50, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_34, c_5381])).
% 10.09/3.95  tff(c_6195, plain, (![C_8674]: (k1_funct_1('#skF_10', '#skF_7'('#skF_10', k2_relat_1('#skF_10'), C_8674))=k1_funct_1('#skF_10', '#skF_8') | ~r2_hidden(C_8674, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_74, c_5416])).
% 10.09/3.95  tff(c_6235, plain, (![C_8674]: (k1_funct_1('#skF_10', '#skF_8')=C_8674 | ~r2_hidden(C_8674, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(C_8674, k2_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_6195, c_32])).
% 10.09/3.95  tff(c_6290, plain, (![C_8709]: (k1_funct_1('#skF_10', '#skF_8')=C_8709 | ~r2_hidden(C_8709, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_74, c_6235])).
% 10.09/3.95  tff(c_6329, plain, (![B_11]: ('#skF_3'(k2_relat_1('#skF_10'), B_11)=k1_funct_1('#skF_10', '#skF_8') | k2_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')=k1_tarski(B_11))), inference(resolution, [status(thm)], [c_24, c_6290])).
% 10.09/3.95  tff(c_6346, plain, (![B_8744]: ('#skF_3'(k2_relat_1('#skF_10'), B_8744)=k1_funct_1('#skF_10', '#skF_8') | k2_relat_1('#skF_10')=k1_tarski(B_8744))), inference(negUnitSimplification, [status(thm)], [c_111, c_6329])).
% 10.09/3.95  tff(c_22, plain, (![A_10, B_11]: ('#skF_3'(A_10, B_11)!=B_11 | k1_xboole_0=A_10 | k1_tarski(B_11)=A_10)), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.09/3.95  tff(c_6360, plain, (![B_8744]: (k1_funct_1('#skF_10', '#skF_8')!=B_8744 | k2_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')=k1_tarski(B_8744) | k2_relat_1('#skF_10')=k1_tarski(B_8744))), inference(superposition, [status(thm), theory('equality')], [c_6346, c_22])).
% 10.09/3.95  tff(c_6412, plain, (k1_tarski(k1_funct_1('#skF_10', '#skF_8'))=k2_relat_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_111, c_6360])).
% 10.09/3.95  tff(c_132, plain, (![A_86, B_87, C_88]: (k2_relset_1(A_86, B_87, C_88)=k2_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 10.09/3.95  tff(c_136, plain, (k2_relset_1(k1_tarski('#skF_8'), '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_132])).
% 10.09/3.95  tff(c_66, plain, (k2_relset_1(k1_tarski('#skF_8'), '#skF_9', '#skF_10')!=k1_tarski(k1_funct_1('#skF_10', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 10.09/3.95  tff(c_137, plain, (k1_tarski(k1_funct_1('#skF_10', '#skF_8'))!=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_66])).
% 10.09/3.95  tff(c_6416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6412, c_137])).
% 10.09/3.95  tff(c_6417, plain, (k1_relat_1('#skF_10')=k1_xboole_0), inference(splitRight, [status(thm)], [c_110])).
% 10.09/3.95  tff(c_6461, plain, (![A_8831, B_8832, C_8833]: (k1_relset_1(A_8831, B_8832, C_8833)=k1_relat_1(C_8833) | ~m1_subset_1(C_8833, k1_zfmisc_1(k2_zfmisc_1(A_8831, B_8832))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.09/3.95  tff(c_6464, plain, (k1_relset_1(k1_tarski('#skF_8'), '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_6461])).
% 10.09/3.95  tff(c_6466, plain, (k1_relset_1(k1_tarski('#skF_8'), '#skF_9', '#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6417, c_6464])).
% 10.09/3.95  tff(c_6589, plain, (![B_8860, A_8861, C_8862]: (k1_xboole_0=B_8860 | k1_relset_1(A_8861, B_8860, C_8862)=A_8861 | ~v1_funct_2(C_8862, A_8861, B_8860) | ~m1_subset_1(C_8862, k1_zfmisc_1(k2_zfmisc_1(A_8861, B_8860))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 10.09/3.95  tff(c_6592, plain, (k1_xboole_0='#skF_9' | k1_relset_1(k1_tarski('#skF_8'), '#skF_9', '#skF_10')=k1_tarski('#skF_8') | ~v1_funct_2('#skF_10', k1_tarski('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_70, c_6589])).
% 10.09/3.95  tff(c_6595, plain, (k1_xboole_0='#skF_9' | k1_tarski('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6466, c_6592])).
% 10.09/3.95  tff(c_6596, plain, (k1_tarski('#skF_8')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_68, c_6595])).
% 10.09/3.95  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.09/3.95  tff(c_6621, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6596, c_20])).
% 10.09/3.95  tff(c_6630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_6621])).
% 10.09/3.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.09/3.95  
% 10.09/3.95  Inference rules
% 10.09/3.95  ----------------------
% 10.09/3.95  #Ref     : 8
% 10.09/3.95  #Sup     : 1367
% 10.09/3.95  #Fact    : 4
% 10.09/3.96  #Define  : 0
% 10.09/3.96  #Split   : 11
% 10.09/3.96  #Chain   : 0
% 10.09/3.96  #Close   : 0
% 10.09/3.96  
% 10.09/3.96  Ordering : KBO
% 10.09/3.96  
% 10.09/3.96  Simplification rules
% 10.09/3.96  ----------------------
% 10.09/3.96  #Subsume      : 472
% 10.09/3.96  #Demod        : 419
% 10.09/3.96  #Tautology    : 374
% 10.09/3.96  #SimpNegUnit  : 132
% 10.09/3.96  #BackRed      : 22
% 10.09/3.96  
% 10.09/3.96  #Partial instantiations: 5271
% 10.09/3.96  #Strategies tried      : 1
% 10.09/3.96  
% 10.09/3.96  Timing (in seconds)
% 10.09/3.96  ----------------------
% 10.09/3.96  Preprocessing        : 0.57
% 10.09/3.96  Parsing              : 0.26
% 10.09/3.96  CNF conversion       : 0.05
% 10.09/3.96  Main loop            : 2.24
% 10.09/3.96  Inferencing          : 0.79
% 10.09/3.96  Reduction            : 0.64
% 10.09/3.96  Demodulation         : 0.44
% 10.09/3.96  BG Simplification    : 0.10
% 10.09/3.96  Subsumption          : 0.59
% 10.09/3.96  Abstraction          : 0.11
% 10.09/3.96  MUC search           : 0.00
% 10.09/3.96  Cooper               : 0.00
% 10.09/3.96  Total                : 2.88
% 10.09/3.96  Index Insertion      : 0.00
% 10.09/3.96  Index Deletion       : 0.00
% 10.09/3.96  Index Matching       : 0.00
% 10.09/3.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
